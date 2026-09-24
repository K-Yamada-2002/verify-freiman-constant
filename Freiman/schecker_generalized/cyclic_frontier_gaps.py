#!/usr/bin/env python3
"""Exact counterexamples to boxed cyclic interval obligations.

A counterexample is at one parameter point in a type's domain. It refutes
that uniform type, not the original fixed-prefix A_n family. Finite outer
approximations only discover gaps; no-gap results never prove filledness.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from explore import Q, state_of, transform
from search_cyclic_types import fl, outer_tail_intervals
from type_graph_geometry import anchor, decode, encode, require, square
from verify_cyclic_types import Verifier


def value(cell, parameters, xy):
    r, s, ratio = parameters
    a, b = cell.anchors()
    x, y = xy
    return square(1+r*a)*x/(1+r*x)+cell.parity*ratio*square(1+s*b)*y/(1+s*y)


@lru_cache(None)
def exact_tails(state, depth):
    result = []
    for letters in product('123', repeat=depth):
        word = ''.join(letters)
        if '31313' in state+word:
            continue
        end = state_of(state+word)
        result.append(tuple(sorted(transform(word, anchor(end, high)) for high in (False, True))))
    return tuple(sorted(result))


def samples(cell, corners=True):
    boxes = (cell.r, cell.s, cell.ratio)
    return tuple(dict.fromkeys([tuple((a+b)/2 for a, b in boxes)]+
                              (list(product(*boxes)) if corners else [])))


def numeric_gaps(cell, parameters, depth, target):
    r, s, ratio = map(fl, parameters)
    a, b = map(fl, cell.anchors())
    def side(x, shape, base):
        return (1+shape*base)**2*x/(1+shape*x)
    left = [(side(x, r, a), side(y, r, a))
            for x, y in outer_tail_intervals(state_of(cell.states[0]), depth)]
    right = [sorted((cell.parity*ratio*side(x, s, b), cell.parity*ratio*side(y, s, b)))
             for x, y in outer_tail_intervals(state_of(cell.states[1]), depth)]
    # A max tree skips right-side gaps absorbed by each left interval.
    # Float output still only proposes a witness for verify_witness below.
    from sum_interval_gaps import sum_gaps
    for lower,upper in sum_gaps(left,right,target):
        if upper>lower+1e-12:
            yield lower,upper


def verify_witness(checker, witness):
    _, cell, lo, hi = checker.node(witness['node'])
    parameters = tuple(map(decode, witness['parameters']))
    require(len(parameters) == 3, 'three witness parameters required')
    require(all(a <= x <= b for x, (a, b) in zip(parameters, (cell.r, cell.s, cell.ratio))),
            'witness outside the type domain')
    low, high = map(decode, witness['gap'])
    require(value(cell, parameters, lo) <= low < high <= value(cell, parameters, hi),
            'gap outside the requested interval')
    depth = witness['depth']
    require(type(depth) is int and depth >= 1, 'positive gap depth required')
    r, s, ratio = parameters
    sides = []
    for state, shape, base, scale in zip(cell.states, (r, s), cell.anchors(), (1, cell.parity*ratio)):
        sides.append(sorted(tuple(sorted(scale*square(1+shape*base)*x/(1+shape*x) for x in pair))
                            for pair in exact_tails(state_of(state), depth)))
    left, right = sides
    i, j, steps = 0, len(right)-1, 0
    while i < len(left) and j >= 0:
        steps += 1
        if left[i][1]+right[j][1] <= low:
            i += 1
        elif left[i][0]+right[j][0] >= high:
            j -= 1
        else:
            raise ValueError('a legal cylinder sum intersects the alleged gap')
    return dict(left_cylinders=len(left), right_cylinders=len(right), comparisons=steps)


def boundary_labels(checker, witness):
    """Recover the exact legal corner on each side of a witnessed gap.

    These labels are new discovery candidates, not filled interval claims.
    Each corner is a pair of finite words followed by legal extremal tails.
    """
    _, cell, _, _ = checker.node(witness['node'])
    r, s, ratio = map(decode, witness['parameters'])
    low, high = map(decode, witness['gap'])
    sides = []
    for state, shape, base, scale in zip(cell.states, (r, s), cell.anchors(), (1, cell.parity*ratio)):
        intervals = []
        state = state_of(state)
        for letters in product('123', repeat=witness['depth']):
            word = ''.join(letters)
            if '31313' in state+word:
                continue
            values = []
            for h in (False, True):
                x = transform(word, anchor(state_of(state+word), h))
                values.append((scale*square(1+shape*base)*x/(1+shape*x), (word, h)))
            intervals.append(tuple(sorted(values)))
        sides.append(sorted(intervals))
    left, right = sides
    j, below = len(right)-1, None
    for _, upper in left:
        while j >= 0 and upper[0]+right[j][1][0] > low:
            j -= 1
        if j >= 0:
            candidate = (upper[0]+right[j][1][0], upper[1]+right[j][1][1])
            if below is None or candidate[0] > below[0]:
                below = candidate
    j, above = len(right), None
    for lower, _ in left:
        while j > 0 and lower[0]+right[j-1][0][0] >= high:
            j -= 1
        if j < len(right):
            candidate = (lower[0]+right[j][0][0], lower[1]+right[j][0][1])
            if above is None or candidate[0] < above[0]:
                above = candidate
    require(below is not None and above is not None, 'gap has no finite outer boundary')
    return dict(lower=below[1], upper=above[1], values=[encode(below[0]), encode(above[0])])


def discover(checker, index, depths=(4, 5), corners=True):
    _, cell, lo, hi = checker.node(index)
    for depth in depths:
        for which, parameters in enumerate(samples(cell, corners)):
            target = tuple(fl(value(cell, parameters, z)) for z in (lo, hi))
            for a, b in numeric_gaps(cell, parameters, depth, target):
                # Stay strictly inside the numerical gap, then replay exactly.
                gap = (Q(F(str((2*a+b)/3))), Q(F(str((a+2*b)/3))))
                row = dict(node=index, depth=depth, sample=which,
                           parameters=list(map(encode, parameters)), gap=list(map(encode, gap)))
                try:
                    row['verification'] = verify_witness(checker, row)
                except ValueError:
                    continue
                return row
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--depths', type=int, nargs='+', default=[4, 5])
    ap.add_argument('--midpoint-only', action='store_true')
    ap.add_argument('--limit', type=int)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--verify', type=Path)
    ap.add_argument('--learn-endpoints', action='store_true')
    args = ap.parse_args()
    checker = Verifier(json.loads(args.graph.read_text()))
    if args.verify:
        data = json.loads(args.verify.read_text())
        require(data['source_proof_hash'] == checker.proof_hash(), 'source graph changed')
        for witness in data['witnesses']:
            verify_witness(checker, witness)
            if 'boundary_labels' in witness:
                require(json.loads(json.dumps(boundary_labels(checker, witness))) == witness['boundary_labels'],
                        'incorrect learned gap boundary')
        print(json.dumps(dict(exact_witnesses=len(data['witnesses']))))
        return
    frontier = [i for i, n in enumerate(checker.nodes) if not n.get('children')]
    if args.limit is not None:
        frontier = frontier[:args.limit]
    result = dict(status='counterexamples to uniform boxed types; no assertion of a gap in A_n',
                  source_proof_hash=checker.proof_hash(), depths=args.depths,
                  surveyed=[], witnesses=[], not_detected=[])
    for index in frontier:
        row = discover(checker, index, args.depths, not args.midpoint_only)
        result['surveyed'].append(index)
        if row is None:
            result['not_detected'].append(index)
        else:
            if args.learn_endpoints:
                row['boundary_labels'] = boundary_labels(checker, row)
            result['witnesses'].append(row)
        print(json.dumps(dict(surveyed=len(result['surveyed']), exact_gaps=len(result['witnesses']),
                              node=index, depth=row['depth'] if row else None)), flush=True)
        if args.output:
            args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
