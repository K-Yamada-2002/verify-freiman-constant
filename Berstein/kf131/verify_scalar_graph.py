#!/usr/bin/env python3
"""Independently verify a finite graph of uniform scalar interval types."""
import argparse
import hashlib
import json
from pathlib import Path

from exact import F, extreme_tail, matrix, state_of, transform
from anchored_geometry import ALPHA, B, difference_range, parameters, transition
from scalar_geometry import uniform_child_core
from verify_type_graph import Verifier, require


class ScalarVerifier(Verifier):
    def __init__(self, data):
        require(data.get('schema') in ('kf131-scalar-intervals-v1', 'kf131-scalar-atlas-v1'),
                'wrong scalar schema')
        super().__init__(data)
        self.atlas = data['schema'] == 'kf131-scalar-atlas-v1'
        self.grid = data['settings']['grid']
        require(type(self.grid) is int and self.grid > 0, 'invalid scalar grid')

    def _box(self, index):
        rb, sb, hb = super()._box(index)
        refinement = self.nodes[index].get('ratio_refinement', [0, 0])
        require(type(refinement) is list and len(refinement) == 2,
                'invalid ratio refinement')
        level, part = refinement
        require(type(level) is int and 0 <= level <= 16 and type(part) is int
                and 0 <= part < 2**level, 'invalid ratio refinement')
        width = (hb[1]-hb[0])/2**level
        return rb, sb, (hb[0]+part*width, hb[0]+(part+1)*width)

    def interval(self, values):
        require(len(values) == 2 and all(type(v) is int for v in values),
                'scalar endpoints must be integers')
        a, b = (F(v, self.grid) for v in values)
        require(a < b, 'scalar interval has no width')
        return a, b

    def proof_hash(self):
        payload = dict(nodes=self.nodes, roots=self.data['roots'],
                       root_prefixes=self.data['root_prefixes'],
                       grid=self.grid, base=str(self.base), bins=self.data['settings']['bins'])
        return hashlib.sha256(json.dumps(payload, sort_keys=True,
                                         separators=(',', ':')).encode()).hexdigest()

    def seed(self):
        require(len(self.data['roots']) == 1, 'one physical seed is required')
        root = self.data['roots'][0]
        require(type(root) is int and 0 <= root < len(self.nodes), 'invalid seed index')
        u, v = self.data['root_prefixes']
        r, s, h, p = parameters(u, v)
        rb, sb, hb = self.box(root)
        require(rb[0] <= r <= rb[1] and sb[0] <= s <= sb[1] and hb[0] <= h <= hb[1]
                and p == self.nodes[root]['parity'], 'actual seed escapes its parameter box')
        require(tuple(map(state_of, (u, v))) == tuple(map(state_of, self.nodes[root]['states'])),
                'wrong actual seed states')
        _, _, c, d = matrix(u)
        scale = (-1)**len(u)/(c*ALPHA+d)**2
        center = transform(u, ALPHA)+transform(v, ALPHA)
        values = sorted(center+scale*t for t in self.interval(self.nodes[root]['interval']))
        require(values[0] < values[1], 'degenerate physical seed')
        return [v.record() for v in values]

    def check_initial_hull(self, index):
        n = self.nodes[index]
        sl, sr = map(state_of, n['states'])
        p = n['parity']
        low = (extreme_tail(sl, False)[0], extreme_tail(sr, p < 0)[0])
        high = (extreme_tail(sl, True)[0], extreme_tail(sr, p > 0)[0])
        lower = difference_range(low, (ALPHA, ALPHA), *self.box(index), p)[1]
        upper = difference_range(high, (ALPHA, ALPHA), *self.box(index), p)[0]
        a, b = self.interval(n['interval'])
        require(lower <= a < b <= upper, 'scalar type escapes the common hull')

    def scalar_child(self, index, edge):
        parent = self.nodes[index]
        u, v = edge['suffixes']
        require(bool(u or v), 'empty non-shrinking successor')
        states = tuple(state_of(s+w) for s, w in zip(parent['states'], (u, v)))
        r, s, h, p = transition(u, v, *self.box(index), parent['parity'])
        cases, dependencies, cores, rectangles = {}, [], [], {}
        for case in edge['cases']:
            swap = case['swap']
            require(type(swap) is bool and swap not in cases, 'invalid or duplicate exchange case')
            child_interval = self.interval(case['interval'])
            boxes = []
            slabs = []
            for j in case['destinations']:
                require(type(j) is int and 0 <= j < len(self.nodes), 'invalid destination index')
                target = self.nodes[j]
                require(tuple(map(state_of, target['states'])) == (states[::-1] if swap else states),
                        'wrong arrival states')
                require(target['parity'] == p, 'wrong arrival parity')
                rb, sb, hb = self.box(j)
                rr, ss = (s, r) if swap else (r, s)
                require(rb[0] <= rr[0] <= rr[1] <= rb[1] and
                        sb[0] <= ss[0] <= ss[1] <= sb[1], 'shape image escapes')
                lo, hi = self.interval(target['interval'])
                if not self.atlas:
                    require(lo <= child_interval[0] < child_interval[1] <= hi,
                            'scalar child interval escapes destination')
                boxes.append(hb)
                slabs.append((hb, (lo, hi)))
                dependencies.append(j)
            require(bool(boxes), 'empty destination list')
            cases[swap] = boxes
            rectangles[swap] = (child_interval, slabs)
            cores.append(uniform_child_core(u, v, swap, child_interval,
                                             *self.box(index), parent['parity']))
        if h[0] <= 1:
            required = h[0], min(h[1], B(1))
            self.covers_ratio(required, cases.get(False, []))
            if self.atlas:
                self.covers_parameter_interval(required, *rectangles[False])
        if h[1] > 1:
            required = 1/h[1], min(1/h[0], B(1))
            self.covers_ratio(required, cases.get(True, []))
            if self.atlas:
                self.covers_parameter_interval(required, *rectangles[True])
        require(bool(cores), 'no child cases')
        common = max(a for a, b in cores), min(b for a, b in cores)
        require(common[0] < common[1], 'child cases have no common uniform interval')
        return common, dependencies

    def covers_parameter_interval(self, hbox, interval, rectangles):
        """Cover the ENTIRE product hbox x interval, not just its projections."""
        cuts = {B.coerce(hbox[0]), B.coerce(hbox[1])}
        for hb, _ in rectangles:
            cuts.update(B.coerce(x) for x in hb if hbox[0] < x < hbox[1])
        cuts = sorted(cuts)
        strips = list(zip(cuts, cuts[1:])) or [(cuts[0], cuts[0])]
        for a, b in strips:
            intervals = [span for hb, span in rectangles if hb[0] <= a <= b <= hb[1]]
            try:
                self.covers_ratio(interval, intervals)
            except ValueError as error:
                raise ValueError('gap in parameter x scalar destination cover') from error

    def local(self, index):
        if index in self.checked:
            return self.checked[index]
        node = self.nodes[index]
        require(node['covered'], f'node {index} is an open obligation')
        self.check_initial_hull(index)
        current, end = self.interval(node['interval'])
        require(bool(node['children']), 'scalar node has no children')
        dependencies = []
        for edge in node['children']:
            (a, b), deps = self.scalar_child(index, edge)
            require(a <= current < b, f'node {index}: uncovered or non-progressing contact')
            current = b
            dependencies.extend(deps)
        require(current >= end, f'node {index}: scalar upper end is not covered')
        result = dict(node=index, children=len(node['children']), dependencies=sorted(set(dependencies)))
        self.checked[index] = result
        return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--audit', action='store_true')
    ap.add_argument('--local', type=int)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    require(not (args.audit and args.local is not None), 'choose audit or local')
    checker = ScalarVerifier(json.loads(args.certificate.read_text()))
    result = checker.audit() if args.audit else (checker.closed() if args.local is None
                                                 else checker.local(args.local))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: (len(v) if isinstance(v, list) else v) for k, v in result.items()}, indent=2))


if __name__ == '__main__':
    main()
