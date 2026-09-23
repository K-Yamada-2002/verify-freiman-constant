#!/usr/bin/env python3
"""Reduce a partial strategy without adding any child obligation.

All changes retain a subsequence of a verified cover and/or a subset of its
destinations. Exact incoming-domain contraction can enable new contacts.
No open interval is declared filled by this optimization.
"""
import argparse
from collections import deque
import copy
from functools import lru_cache
import hashlib
import json
from pathlib import Path

from chart_geometry import compare
from contract_piecewise_charts import contract, edges, prune, rules
from type_graph_geometry import endpoint
from verify_piecewise_charts import PiecewiseVerifier


@lru_cache(maxsize=200000)
def popcount(mask):
    return bin(mask).count('1')


def dependencies(data):
    return [set(d['node'] for e in edges(n) for d in e['destinations']) for n in data['nodes']]


def frontier_masks(data):
    """Exact open descendants of every node, including directed cycles."""
    children = dependencies(data)
    parents = [set() for _ in children]
    masks = [0]*len(children)
    queue = deque()
    for i, node in enumerate(data['nodes']):
        for j in children[i]:
            parents[j].add(i)
        if not node.get('children') and not node.get('pieces'):
            masks[i] = 1 << i
            queue.append(i)
    queued = set(queue)
    while queue:
        i = queue.popleft()
        queued.remove(i)
        for parent in parents[i]:
            new = masks[parent] | masks[i]
            if new != masks[parent]:
                masks[parent] = new
                if parent not in queued:
                    queue.append(parent)
                    queued.add(parent)
    return masks


def pareto_labels(labels, limit=32):
    """Bounded discovery beam; discarded labels never establish impossibility."""
    result = []
    for label in sorted(labels, key=lambda z: (popcount(z[0]), popcount(z[1]), len(z[2]), z[2])):
        if any((a | label[0]) == label[0] and (b | label[1]) == label[1]
               and len(path) <= len(label[2]) for a, b, path in result):
            continue
        result.append(label)
        if len(result) >= limit:
            break
    return result


def cover_subsequence(checker, domain, lower, upper, plan, masks, beam=32):
    """Choose a full exact cover using only the original ordered edges."""
    labels = []
    ends = [(endpoint(domain.states, e['lower'], e['suffixes']),
             endpoint(domain.states, e['upper'], e['suffixes'])) for e in plan]
    for i, (a, b) in enumerate(ends):
        frontier, direct = 0, 0
        for d in plan[i]['destinations']:
            frontier |= masks[d['node']]
            direct |= 1 << d['node']
        choices = []
        if compare(domain, lower, a) and compare(domain, b, lower, strict=True):
            choices.append((frontier, direct, (i,)))
        for j in range(i):
            if labels[j] and compare(domain, ends[j][1], a) and compare(domain, b, ends[j][1], strict=True):
                choices.extend((f | frontier, ds | direct, path+(i,)) for f, ds, path in labels[j])
        labels.append(pareto_labels(choices, beam))
    candidates = [label for i, (a, b) in enumerate(ends) if compare(domain, b, upper) for label in labels[i]]
    if not candidates:
        return None
    best = min(candidates, key=lambda z: (popcount(z[0]), popcount(z[1]), len(z[2]), z[2]))
    return [plan[i] for i in best[2]]


def trim(checker, beam=32):
    masks = frontier_masks(checker.data)
    summary = dict(removed_cover_edges=0, removed_destination_references=0, shortened_rules=0)
    before = dependencies(checker.data)
    for i, node in enumerate(checker.nodes):
        if not node.get('children') and not node.get('pieces'):
            continue
        _, domain, lower, upper = checker.node(i)
        changed = False
        for rule in rules(node):
            part = checker.cells[rule['cell']]
            plan = rule['children']
            # Remove an individually redundant destination only after the
            # unchanged exact child verifier confirms whole-image coverage.
            for edge in plan:
                for dest in sorted(edge['destinations'][:],
                                   key=lambda d: popcount(masks[d['node']]), reverse=True):
                    if len(edge['destinations']) <= 1:
                        break
                    old = edge['destinations'][:]
                    edge['destinations'].remove(dest)
                    try:
                        checker.child(part, edge)
                    except ValueError:
                        edge['destinations'] = old
                    else:
                        changed = True
                        summary['removed_destination_references'] += 1
            selected = cover_subsequence(checker, part, lower, upper, plan, masks, beam)
            if selected is None:
                raise ValueError('lost the original verified cover during subsequence search')
            if len(selected) < len(plan):
                summary['removed_cover_edges'] += len(plan)-len(selected)
                plan[:] = selected
                changed = True
        if changed:
            summary['shortened_rules'] += 1
            checker.checked.pop(i, None)
            checker.local(i)
    after = dependencies(checker.data)
    if not all(new <= old for old, new in zip(before, after)):
        raise ValueError('frontier reducer introduced a new obligation')
    return summary


def counts(data):
    masks = frontier_masks(data)
    local = [i for i, n in enumerate(data['nodes']) if n.get('children') or n.get('pieces')]
    return dict(nodes=len(data['nodes']), local=len(local), open=len(data['nodes'])-len(local),
                closed_supported_types=sum(masks[i] == 0 for i in local))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--rounds', type=int, default=4)
    ap.add_argument('--beam', type=int, default=32)
    ap.add_argument('--no-contract', action='store_true')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.rounds < 1 or args.beam < 1:
        ap.error('positive round and beam limits required')
    data = json.loads(args.graph.read_text())
    checker = PiecewiseVerifier(data)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('input has invalid local rules')
    initial = counts(data)
    data.setdefault('frontier_reduction_sources', []).append(dict(path=str(args.graph),
        proof_hash=checker.proof_hash(), source_counts=initial,
        algorithm_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()))
    print(json.dumps(dict(initial=initial)), flush=True)
    history = data.setdefault('frontier_reduction_history', [])
    for step in range(args.rounds):
        row = dict(round=len(history))
        if not args.no_contract:
            row['contraction'] = contract(checker)
        row['trimming'] = trim(checker, args.beam)
        data = prune(data)
        checker = PiecewiseVerifier(data)
        audit = checker.audit()
        if audit['failed_rules']:
            raise ValueError('reduced strategy failed exact replay')
        row.update(counts(data), proof_hash=checker.proof_hash())
        if row['open'] > initial['open'] or row['nodes'] > initial['nodes']:
            raise ValueError('reduction increased the root obligations')
        history.append(row)
        data['frontier_reduction_history'] = history
        print(json.dumps(row), flush=True)
        temporary = args.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(data, indent=2)+'\n')
        temporary.replace(args.output)
        args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
        if not any(row['trimming'].values()) and (args.no_contract or not any(row['contraction'].values())):
            break
    try:
        result = checker.closed()
    except ValueError as error:
        result = dict(closed=False, reason=str(error))
        args.output.with_suffix('.verified.json').unlink(missing_ok=True)
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(final=counts(data), verification=result)), flush=True)


if __name__ == '__main__':
    main()
