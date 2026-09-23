#!/usr/bin/env python3
"""Compile existing proper-digit cover recipes on existing types.

Only recipes whose destinations are already reachable are considered. A copied
recipe is verified afresh on the requesting domain; no zero-digit implication
edge and no new type is introduced. The interval goal is unchanged.
Optionally replace local rules when the old graph predicts fewer distinct
open descendants. This is a discovery score, not an optimality guarantee.
"""
import argparse
from collections import defaultdict
import copy
import json
from pathlib import Path
import time

from contract_piecewise_charts import edges, prune
from reduce_chart_frontier import counts, cover_subsequence, frontier_masks, popcount
from type_graph_geometry import endpoint
from verify_piecewise_charts import PiecewiseVerifier


def reachable(data):
    todo = list(data['roots'].values())
    seen = set()
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        todo.extend(d['node'] for e in edges(data['nodes'][i]) for d in e['destinations'])
    return seen


def install_recipe(checker, index, recipe, masks, beam=32, replace_local=False):
    node, domain, lower, upper = checker.node(index)
    was_local = bool(node.get('children') or node.get('pieces'))
    if was_local and not replace_local:
        raise ValueError('recipe target must still be unresolved')
    selected = cover_subsequence(checker, domain, lower, upper, recipe, masks, beam)
    if selected is None:
        return False, 'contacts do not cover the whole target'
    if was_local:
        footprint = 0
        for edge in selected:
            for dest in edge['destinations']:
                footprint |= masks[dest['node']]
        if popcount(footprint) >= popcount(masks[index]):
            return False, 'no strict frontier improvement'
    old = node['children']
    old_pieces = node.pop('pieces', None)
    node['children'] = copy.deepcopy(selected)
    checker.checked.pop(index, None)
    try:
        checker.local(index)
    except ValueError as error:
        node['children'] = old
        if old_pieces is not None:
            node['pieces'] = old_pieces
        checker.checked.pop(index, None)
        return False, str(error)
    return True, None


def reuse(checker, seconds=180, candidates=32, beam=32, progress=None, optimize_local=False):
    start = time.monotonic()
    active = reachable(checker.data)
    masks = frontier_masks(checker.data)
    groups, seen_recipes = defaultdict(list), defaultdict(dict)
    boxes, goals, incoming = {}, {}, defaultdict(int)
    for i in sorted(active):
        node = checker.nodes[i]
        domain = checker.cells[node['cell']]
        boxes[i] = tuple(tuple(float(x.decimal()) for x in b) for b in (domain.r, domain.s, domain.ratio))
        goals[i] = tuple(endpoint(domain.states, node[k]) for k in ('lower', 'upper'))
        for edge in edges(node):
            for dest in edge['destinations']:
                incoming[dest['node']] += 1
        if node.get('pieces') or not node.get('children'):
            continue  # A guarded recipe needs a separate guard pullback.
        signature = domain.states, domain.parity, domain.high
        encoded = json.dumps(node['children'], sort_keys=True, separators=(',', ':'))
        record = seen_recipes[signature].get(encoded)
        if record is None:
            record = dict(source=i, plan=node['children'], owners=[])
            seen_recipes[signature][encoded] = record
            groups[signature].append(record)
        record['owners'].append(i)
    opened = [i for i in active if not checker.nodes[i].get('children') and not checker.nodes[i].get('pieces')]
    targets = sorted(active if optimize_local else opened, key=lambda i: (-incoming[i], i))
    stats = dict(initial_open=len(opened), inspected=0, recipe_attempts=0, accepted=0,
                 improved_local=0, no_improvement=0, contact_failures=0, exact_failures=0,
                 recipes=sum(map(len, groups.values())), stop='finished menu')
    accepted = []
    for i in targets:
        if time.monotonic()-start >= seconds:
            stats['stop'] = 'time limit'
            break
        node = checker.nodes[i]
        was_local = bool(node.get('children') or node.get('pieces'))
        if was_local and not masks[i]:
            continue
        domain = checker.cells[node['cell']]
        options = []
        for recipe in groups[domain.states, domain.parity, domain.high]:
            # Floating outer boxes only rank/filter discovery candidates.
            # Every selected cover is checked on the actual correlated domain.
            same = any(goals[j] == goals[i] for j in recipe['owners'])
            overlap = any(all(max(a[0], b[0]) <= min(a[1], b[1])+1e-12
                              for a, b in zip(boxes[j], boxes[i])) for j in recipe['owners'])
            if not same and not overlap:
                continue
            contained = any(all(a[0] <= b[0]+1e-12 and b[1] <= a[1]+1e-12
                                for a, b in zip(boxes[j], boxes[i])) for j in recipe['owners'])
            footprint = 0
            for e in recipe['plan']:
                for dest in e['destinations']:
                    footprint |= masks[dest['node']]
            options.append(((not contained, not same, popcount(footprint), recipe['source']), recipe))
        stats['inspected'] += 1
        for _, recipe in sorted(options, key=lambda row: row[0])[:candidates]:
            if time.monotonic()-start >= seconds:
                stats['stop'] = 'time limit'
                break
            stats['recipe_attempts'] += 1
            success, error = install_recipe(checker, i, recipe['plan'], masks, beam, optimize_local)
            if success:
                stats['improved_local' if was_local else 'accepted'] += 1
                accepted.append(dict(node=i, source=recipe['source'], replaced_local=was_local))
                break
            if error == 'contacts do not cover the whole target':
                stats['contact_failures'] += 1
            elif error == 'no strict frontier improvement':
                stats['no_improvement'] += 1
            else:
                stats['exact_failures'] += 1
        if progress and stats['inspected'] % 100 == 0:
            progress(stats)
    remaining = reachable(checker.data)
    if not remaining <= active or (not optimize_local and remaining != active):
        raise ValueError('recipe reuse introduced new reachable types')
    final_open = sum(not checker.nodes[i].get('children') and not checker.nodes[i].get('pieces') for i in active)
    if final_open != len(opened)-stats['accepted']:
        raise ValueError('recipe reuse did not preserve unresolved obligations')
    stats['elapsed_seconds'] = time.monotonic()-start
    return dict(statistics=stats, accepted=accepted)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--seconds', type=float, default=180)
    ap.add_argument('--candidates', type=int, default=32)
    ap.add_argument('--beam', type=int, default=32)
    ap.add_argument('--optimize-local', action='store_true', help='also replace local rules by recipes with fewer open descendants')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.seconds <= 0 or min(args.candidates, args.beam) < 1:
        ap.error('positive discovery limits required')
    data = prune(json.loads(args.graph.read_text()))
    checker = PiecewiseVerifier(data)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('input has invalid local rules')
    before = counts(data)
    data.setdefault('recipe_reuse_sources', []).append(dict(path=str(args.graph), proof_hash=checker.proof_hash(), counts=before))
    print(json.dumps(dict(initial=before)), flush=True)
    result = reuse(checker, args.seconds, args.candidates, args.beam,
                   lambda s: print(json.dumps(s), flush=True), args.optimize_local)
    data.setdefault('recipe_reuse_history', []).append(result)
    data = prune(data)
    checker = PiecewiseVerifier(data)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('new recipe failed independent local replay')
    temp = args.output.with_suffix('.tmp')
    temp.write_text(json.dumps(data, indent=2)+'\n')
    temp.replace(args.output)
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    try:
        verdict = checker.closed()
    except ValueError as error:
        verdict = dict(closed=False, reason=str(error))
        args.output.with_suffix('.verified.json').unlink(missing_ok=True)
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(verdict, indent=2)+'\n')
    print(json.dumps(dict(final=counts(data), reuse=result['statistics'], verification=verdict)), flush=True)


if __name__ == '__main__':
    main()
