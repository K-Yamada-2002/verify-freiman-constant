#!/usr/bin/env python3
"""Infer ratio guards from a rule, then reuse rules across artificial bins.

Every widening and redirection is replayed by the unchanged exact verifier.
Open nodes remain obligations. This optimizer cannot certify an open graph.
"""
import argparse
import copy
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

from explore import Q, state_of
from type_graph_geometry import Cell, delta_range, endpoint, full_labels, ge, swapped, transition
from verify_cyclic_types import Verifier, contains_box


def ratio_guard(cell, comparisons, bounds):
    """Largest closed R subinterval where every uniform comparison holds.

    With r,s independent and R>0, min(F(a)-F(b))=A+B R exactly;
    A and B are the separate one-variable minima in Q(sqrt(462)).
    """
    low, high = bounds
    alpha, beta = cell.anchors()
    for first, second in comparisons:
        a = delta_range(alpha, first[0], second[0], cell.r)[0]
        right = delta_range(beta, first[1], second[1], cell.s)
        b = right[0] if cell.parity > 0 else -right[1]
        if b > 0:
            low = max(low, -a/b)
        elif b < 0:
            high = min(high, -a/b)
        elif a < 0:
            return None
        if low > high:
            return None
    return low, high


def envelope(checker, index, cap=(Q(F(1, 64)), Q(64))):
    node, cell, lower, upper = checker.node(index)
    hull = [endpoint(cell.states, z) for z in full_labels(cell.parity)]
    comparisons = [(upper, lower), (lower, hull[0]), (hull[1], upper)]
    current = lower
    unit = Cell(cell.states, cell.parity, cell.high, cell.r, cell.s, (Q(1), Q(1)))
    low, high = min(cap[0], cell.ratio[0]), max(cap[1], cell.ratio[1])
    for edge in node['children']:
        u, v = edge['suffixes']
        a, b = (endpoint(cell.states, edge[k], (u, v)) for k in ('lower', 'upper'))
        comparisons.extend(((current, a), (b, current), (b, a)))
        current = b
        image = transition(unit, u, v, edge['high'])
        boxes, invariant_self = [], False
        for d in edge['destinations']:
            tc = checker.cells[checker.nodes[d['node']]['cell']]
            tc = swapped(tc) if d['swap'] else tc
            if contains_box(tc.r, image.r) and contains_box(tc.s, image.s):
                # A true unit-multiplier return is valid on an enlarged ratio
                # interval too. The subsequent exact replay checks everything.
                if d['node'] == index and not d['swap'] and image.ratio == (Q(1), Q(1)):
                    invariant_self = True
                boxes.append(tc.ratio)
        if invariant_self:
            continue
        merged = []
        for left, right in sorted(boxes):
            if merged and left <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(merged[-1][1], right))
            else:
                merged.append((left, right))
        options = [(a/image.ratio[0], b/image.ratio[1]) for a, b in merged]
        possible = [r for r in options if contains_box(r, cell.ratio)]
        if not possible:
            # Some refined destinations cover r,s only collectively. Keep
            # those unchanged rather than infer a guard from insufficient data.
            return cell.ratio
        left, right = max(possible, key=lambda z: z[1]-z[0])
        low, high = max(low, left), min(high, right)
    comparisons.append((current, upper))
    return ratio_guard(cell, comparisons, (low, high))


def incoming(nodes):
    parents = defaultdict(set)
    for i, node in enumerate(nodes):
        for e in node['children']:
            for d in e['destinations']:
                parents[d['node']].add(i)
    return parents


def widen(checker):
    parents = incoming(checker.nodes)
    accepted = []
    for i, node in enumerate(checker.nodes):
        if not node['children']:
            continue
        checker.local(i)
        old_index = node['cell']
        old = checker.cells[old_index]
        bounds = envelope(checker, i)
        if bounds is None or bounds == old.ratio:
            continue
        if not contains_box(bounds, old.ratio):
            raise ValueError('guard inference lost part of the verified original domain')
        success = False
        # Boundary equalities can destroy strict progress. Back off to the
        # interior; also try one-sided widening when an incoming offer blocks
        # expansion at only one end.
        for target in (bounds, (bounds[0], old.ratio[1]), (old.ratio[0], bounds[1])):
            for power in (0, 1, 2, 4):
                q = tuple(a+(b-a)/2**power for a, b in zip(old.ratio, target))
                if q == old.ratio:
                    continue
                candidate = Cell(old.states, old.parity, old.high, old.r, old.s, q)
                node['cell'] = len(checker.cells)
                checker.cells.append(candidate)
                checker.checked.clear()
                try:
                    checker.local(i)
                    for p in parents[i]:
                        checker.local(p)
                    checker.seeds()
                except ValueError:
                    node['cell'] = old_index
                    checker.cells.pop()
                    checker.checked.clear()
                    continue
                checker.data['cells'].append(candidate.record())
                accepted.append(i)
                success = True
                break
            if success:
                break
    return accepted


def fold(checker):
    groups = defaultdict(list)
    for i, n in enumerate(checker.nodes):
        if n['children']:
            c = checker.cells[n['cell']]
            groups[tuple(map(state_of, c.states)), c.parity, c.high].append(i)
    changed = 0
    removed_references = 0
    for i, n in enumerate(checker.nodes):
        parent = checker.cells[n['cell']]
        for edge in n['children']:
            if len(edge['destinations']) == 1 and checker.nodes[edge['destinations'][0]['node']]['children']:
                continue
            image = transition(parent, *edge['suffixes'], edge['high'])
            old = edge['destinations']
            found = False
            for swap in (False, True):
                actual = swapped(image) if swap else image
                candidates = groups[actual.states, actual.parity, actual.high]
                for j in sorted(candidates, key=lambda j: j != i):
                    c = checker.cells[checker.nodes[j]['cell']]
                    if not all(contains_box(a, b) for a, b in zip(
                            (c.r, c.s, c.ratio), (actual.r, actual.s, actual.ratio))):
                        continue
                    edge['destinations'] = [dict(node=j, swap=swap)]
                    try:
                        checker.child(parent, edge)
                    except ValueError:
                        edge['destinations'] = old
                        continue
                    changed += 1
                    removed_references += len(old)-1
                    found = True
                    break
                if found:
                    break
            if not found:
                edge['destinations'] = old
    checker.checked.clear()
    return dict(changed_edges=changed, removed_references=removed_references)


def prune(data):
    reached, pending = set(), list(data['roots'].values())
    while pending:
        i = pending.pop()
        if i in reached:
            continue
        reached.add(i)
        pending.extend(d['node'] for e in data['nodes'][i]['children'] for d in e['destinations'])
    ids = {old: new for new, old in enumerate(sorted(reached))}
    used = sorted({data['nodes'][i]['cell'] for i in reached})
    cids = {old: new for new, old in enumerate(used)}
    nodes = []
    for i in sorted(reached):
        n = copy.deepcopy(data['nodes'][i])
        n['cell'] = cids[n['cell']]
        for e in n['children']:
            for d in e['destinations']:
                d['node'] = ids[d['node']]
        nodes.append(n)
    data['nodes'], data['cells'] = nodes, [data['cells'][i] for i in used]
    data['roots'] = {k: ids[i] for k, i in data['roots'].items()}
    data.pop('search', None)  # The old search counts no longer describe this graph.
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--rounds', type=int, default=2)
    args = ap.parse_args()
    data = json.loads(args.graph.read_text())
    original = Verifier(data)
    initial = original.audit()
    if initial['failed_rules']:
        raise ValueError('input has invalid local rules')
    data.setdefault('compaction_sources', []).append(dict(path=str(args.graph), proof_hash=original.proof_hash()))
    history = []
    for iteration in range(args.rounds):
        checker = Verifier(data)
        grown = widen(checker)
        row = dict(round=iteration, widened=len(grown), **fold(checker))
        data = prune(data)
        audit = Verifier(data).audit()
        if audit['failed_rules']:
            raise AssertionError(audit['failed_rules'])
        row.update(nodes=len(data['nodes']), open=len(audit['open_nodes']), verified=len(audit['verified_rules']))
        history.append(row)
        data['compaction'] = history
        args.output.write_text(json.dumps(data, indent=2)+'\n')
        args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
        print(json.dumps(row), flush=True)
        if not audit['open_nodes']:
            result = Verifier(data).closed()
            args.output.with_suffix('.verified.json').write_text(json.dumps(result, indent=2)+'\n')
            print(json.dumps(result), flush=True)
            break
        if not grown and not row['changed_edges']:
            break


if __name__ == '__main__':
    main()
