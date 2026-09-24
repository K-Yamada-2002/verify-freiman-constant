#!/usr/bin/env python3
"""Exact gap witnesses on correlated chart domains, including guarded graphs.

A witness refutes a uniform node obligation, not the original A_n family:
the parameter point may be an unreachable point of the enclosing domain.
Numerical discovery is never used to assert filledness or absence of gaps.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

from chart_geometry import Domain, relative_box
from contract_piecewise_charts import edges, rules
from cyclic_frontier_gaps import discover, samples, verify_witness
from type_graph_geometry import Cell, decode, encode, require
from verify_cyclic_types import Verifier
from verify_piecewise_charts import PiecewiseVerifier


def point_checker(checker, index, point):
    node, domain, _, _ = checker.node(index)
    base = domain.base
    require(len(point) == 3 and all(a <= x <= b for x, (a, b) in
            zip(point, (base.r, base.s, base.ratio))), 'point outside base chart')
    singleton = Cell(base.states, base.parity, base.high,
                     *((x, x) for x in point)).validate()
    actual = Domain(singleton, domain.words, domain.high).validate().outer
    require(all(a == b for a, b in (actual.r, actual.s, actual.ratio)),
            'point chart image is not a point')
    return Verifier(dict(format='freiman-cyclic-types-v1',
        cells=[actual.record()], nodes=[dict(cell=0, lower=node['lower'],
        upper=node['upper'], children=[])], roots={}))


def replay(checker, row):
    point = tuple(map(decode, row['base_parameters']))
    local = point_checker(checker, row['node'], point)
    return verify_witness(local, row['witness'])


def probe(checker, index, depths):
    domain = checker.cells[checker.nodes[index]['cell']]
    for point in samples(domain.base):
        local = point_checker(checker, index, point)
        witness = discover(local, 0, depths, corners=False)
        if witness is not None:
            row = dict(node=index, base_parameters=list(map(encode, point)),
                       witness=witness)
            row['exact_replay'] = replay(checker, row)
            return row
    return None


def backward_trace(checker, row, depth=6):
    """Trace a parameter witness through every saved incoming guard/edge.

    Exclusion is exact. A root-box hit, depth limit, or cycle is inconclusive
    about actual A_n points and about other representations of a target value.
    """
    replay(checker, row)
    incoming = [[] for _ in checker.nodes]
    for i, node in enumerate(checker.nodes):
        for rule in rules(node):
            part = checker.cells[rule['cell']]
            for edge in rule['children']:
                child = part.extend(*edge['suffixes'], edge['high'])
                for dest in edge['destinations']:
                    incoming[dest['node']].append((i, part, child, dest['swap']))
    roots = set(checker.data['roots'].values())

    def trace(index, point, remaining, seen):
        if index in roots:
            return dict(node=index, status='possible_from_root_box')
        key = index, point
        if key in seen:
            return dict(node=index, status='inconclusive_cycle')
        if remaining == 0:
            return dict(node=index, status='inconclusive_depth')
        actual = point_checker(checker, index, point).cells[0]
        source = Domain(actual, ('', ''), actual.high)
        branches = []
        for parent, guard, child, swap in incoming[index]:
            image = relative_box(source.exchange() if swap else source, child)
            bounds = None if image is None else (image.r, image.s, image.ratio)
            if bounds is None or not all(a <= lo == hi <= b for (lo, hi), (a, b)
                    in zip(bounds, (guard.base.r, guard.base.s, guard.base.ratio))):
                branches.append(dict(node=parent, status='outside_parent_guard'))
                continue
            branches.append(trace(parent, tuple(a for a, b in bounds), remaining-1,
                                  seen | {key}))
        excluded = all(b['status'] in ('excluded', 'outside_parent_guard') for b in branches)
        return dict(node=index, status='excluded' if excluded else 'inconclusive',
                    parents=branches)

    require(depth >= 0, 'negative trace depth')
    return trace(row['node'], tuple(map(decode, row['base_parameters'])), depth, frozenset())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--limit', type=int, default=32)
    ap.add_argument('--depths', type=int, nargs='+', default=[4, 5])
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--verify', action='store_true')
    ap.add_argument('--backward-depth', type=int)
    args = ap.parse_args()
    if args.limit < 1 or min(args.depths) < 1:
        ap.error('positive limits and depths required')
    checker = PiecewiseVerifier(json.loads(args.graph.read_text()))
    checker.seeds()
    if args.verify:
        result = json.loads(args.output.read_text())
        require(result['source_proof_hash'] == checker.proof_hash(), 'source changed')
        for row in result['witnesses']:
            require(replay(checker, row) == row['exact_replay'], 'replay differs')
            if 'backward_trace' in row:
                require(backward_trace(checker, row, result['backward_depth']) ==
                        row['backward_trace'], 'backward replay differs')
        print(json.dumps(dict(exact_witnesses=len(result['witnesses']))))
        return
    incoming = Counter(d['node'] for n in checker.nodes for e in edges(n)
                       for d in e['destinations'])
    opened = [i for i, n in enumerate(checker.nodes)
              if not n.get('children') and not n.get('pieces')]
    targets = sorted(opened, key=lambda i: (-incoming[i], i))[:args.limit]
    result = dict(status='uniform chart counterexamples only; no gap claim for A_n',
                  source_proof_hash=checker.proof_hash(), depths=args.depths,
                  backward_depth=args.backward_depth,
                  surveyed=[], witnesses=[], not_detected=[])
    for i in targets:
        row = probe(checker, i, args.depths)
        result['surveyed'].append(i)
        if row is None:
            result['not_detected'].append(i)
        else:
            if args.backward_depth is not None:
                row['backward_trace'] = backward_trace(checker, row, args.backward_depth)
            result['witnesses'].append(row)
        tmp = args.output.with_suffix('.tmp')
        tmp.write_text(json.dumps(result, indent=2)+'\n')
        tmp.replace(args.output)
        print(json.dumps(dict(node=i, surveyed=len(result['surveyed']),
                              gaps=len(result['witnesses']))), flush=True)


if __name__ == '__main__':
    main()
