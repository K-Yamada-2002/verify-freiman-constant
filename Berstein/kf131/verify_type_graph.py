#!/usr/bin/env python3
"""Replay an anchored interval-type graph, including all return obligations.

Use --local NODE to certify one cover without asserting graph closure.
Without --local, every reachable node must have a complete verified cover.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

from exact import F, state_of, transform
from anchored_geometry import B, difference_range, endpoint_pair, parameters, transition


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exchange(label):
    a, h, b, k = label
    return b, k, a, h


@lru_cache(None)
def shape_box(word):
    lo, hi = F(1, 4), F(4, 5)
    for digit in word:
        lo, hi = 1/(int(digit)+hi), 1/(int(digit)+lo)
    return lo, hi


class Verifier:
    def __init__(self, data):
        self.data = data
        self.nodes = data['nodes']
        self.base = F(str(data['settings']['base']))
        require(0 < self.base < 1, 'invalid ratio grid')
        self.checked = {}
        self.box = lru_cache(None)(self._box)
        self.points = lru_cache(None)(self._points)

    def proof_hash(self):
        payload = {'nodes': self.nodes, 'roots': self.data['roots'],
                   'root_prefixes': self.data['root_prefixes'],
                   'base': str(self.base), 'bins': self.data['settings']['bins']}
        return hashlib.sha256(json.dumps(payload, sort_keys=True,
                                         separators=(',', ':')).encode()).hexdigest()

    def seed(self):
        require(len(self.data['roots']) == 1, 'one physical seed is required')
        root = self.data['roots'][0]
        require(type(root) is int and 0 <= root < len(self.nodes), 'invalid seed index')
        u, v = self.data['root_prefixes']
        r, s, h, parity = parameters(u, v)
        rb, sb, hb = self.box(root)
        require(rb[0] <= r <= rb[1] and sb[0] <= s <= sb[1]
                and hb[0] <= h <= hb[1] and self.nodes[root]['parity'] == parity,
                'actual seed is outside its parameter domain')
        require(tuple(map(state_of, (u, v))) ==
                tuple(map(state_of, self.nodes[root]['states'])), 'wrong seed states')
        points = self.points(root)
        extension_field = any(isinstance(value, B) for point in points for value in point)
        ends = sorted((B.coerce(transform(u, x))+B.coerce(transform(v, y)))
                      if extension_field else transform(u, x)+transform(v, y)
                      for x, y in points)
        require(ends[0] < ends[1], 'degenerate physical seed interval')
        return [z.record() for z in ends]

    def _box(self, index):
        node = self.nodes[index]
        i = node['ratio_bin']
        require(type(i) is int and 0 <= i < self.data['settings']['bins'], 'invalid ratio bin')
        require(node['parity'] in (-1, 1), 'invalid parity')
        return (shape_box(node['states'][0]), shape_box(node['states'][1]),
                (self.base**(i+1), self.base**i))

    def _points(self, index):
        node = self.nodes[index]
        return tuple(endpoint_pair(node['states'], node[key]) for key in ('lower', 'upper'))

    def ge(self, index, a, b, strict=False):
        value = difference_range(a, b, *self.box(index), self.nodes[index]['parity'])[0]
        return value > 0 if strict else value >= 0

    def covers_ratio(self, interval, boxes):
        current, end = map(B.coerce, interval)
        require(bool(boxes), 'missing image destination')
        for lo, hi in sorted(boxes):
            if hi < current:
                continue
            require(lo <= current, 'gap between destination parameter boxes')
            current = max(current, B(hi))
            if current >= end:
                return
        require(current >= end, 'destination boxes do not cover the image')

    def child(self, index, edge):
        parent = self.nodes[index]
        u, v = edge['suffixes']
        require(bool(u or v), 'non-shrinking empty successor')
        states = tuple(state_of(s+w) for s, w in zip(parent['states'], (u, v)))
        mapped = [endpoint_pair(parent['states'], edge[key], (u, v))
                  for key in ('lower', 'upper')]
        require(self.ge(index, mapped[1], mapped[0], strict=True), 'child width not uniformly positive')
        r, s, h, parity = transition(u, v, *self.box(index), parent['parity'])
        destinations = {False: [], True: []}
        dependencies = []
        for dest in edge['destinations']:
            j, swap = dest['node'], dest['swap']
            require(type(j) is int and 0 <= j < len(self.nodes), 'invalid destination index')
            require(type(swap) is bool, 'invalid exchange flag')
            target = self.nodes[j]
            expected_states = states[::-1] if swap else states
            require(tuple(map(state_of, target['states'])) == expected_states, 'wrong arrival states')
            require(target['parity'] == parity, 'wrong arrival parity')
            rb, sb, hb = self.box(j)
            rr, ss = (s, r) if swap else (r, s)
            require(rb[0] <= rr[0] <= rr[1] <= rb[1], 'left shape image escapes')
            require(sb[0] <= ss[0] <= ss[1] <= sb[1], 'right shape image escapes')
            low, high = self.points(j)
            for key in ('lower', 'upper'):
                label = exchange(edge[key]) if swap else edge[key]
                point = endpoint_pair(target['states'], label)
                require(self.ge(j, point, low) and self.ge(j, high, point),
                        'offered endpoint escapes destination interval type')
            destinations[swap].append(hb)
            dependencies.append(j)
        # Closed grid endpoints may be assigned to either adjacent box.
        # Merely listing intersecting destination cells is insufficient.
        if h[0] <= 1:
            self.covers_ratio((h[0], min(h[1], B(1))), destinations[False])
        if h[1] > 1:
            self.covers_ratio((1/h[1], min(1/h[0], B(1))), destinations[True])
        return tuple(mapped), dependencies

    def local(self, index):
        if index in self.checked:
            return self.checked[index]
        node = self.nodes[index]
        require(node['covered'], f'node {index} is an open obligation')
        lo, hi = self.points(index)
        require(self.ge(index, hi, lo, strict=True), f'node {index} width is not positive')
        require(bool(node['children']), f'node {index} has no children')
        current = lo
        deps = []
        for number, edge in enumerate(node['children']):
            (a, b), child_deps = self.child(index, edge)
            require(self.ge(index, current, a), f'node {index}: uncovered contact')
            # The first interval may end below the target's lower endpoint
            # for some parameters. Its own positive width is checked in
            # child(); the entire connected chain covers the target once
            # its last upper endpoint passes the target's upper endpoint.
            if number:
                require(self.ge(index, b, current, strict=True), f'node {index}: non-progressing offer')
            current = b
            deps.extend(child_deps)
        require(self.ge(index, current, hi), f'node {index}: upper end not covered')
        result = {'node': index, 'children': len(node['children']),
                  'dependencies': sorted(set(deps))}
        self.checked[index] = result
        return result

    def closed(self):
        require(bool(self.data['roots']), 'empty root list')
        pending = list(self.data['roots'])
        reached = set()
        while pending:
            index = pending.pop()
            require(type(index) is int and 0 <= index < len(self.nodes), 'invalid root or dependency')
            if index in reached:
                continue
            reached.add(index)
            pending.extend(self.local(index)['dependencies'])
        return {'status': 'closed interval-type graph verified exactly',
                'verified_nodes': len(reached), 'root_interval': self.seed(),
                'proof_hash': self.proof_hash()}

    def audit(self):
        """Certify all available local rules, leaving open nodes explicit."""
        seed = self.seed()
        verified, open_nodes, failed = [], [], []
        for i, node in enumerate(self.nodes):
            if not node['covered']:
                open_nodes.append(i)
                continue
            try:
                verified.append(self.local(i))
            except ValueError as error:
                failed.append({'node': i, 'error': str(error)})
            if (len(verified)+len(failed)) % 100 == 0:
                print(f'verified {len(verified)} local rules; failed {len(failed)}',
                      file=sys.stderr, flush=True)
        return {'status': 'exact local-rule audit; open nodes are remaining induction obligations',
                'verified_rules': verified, 'open_nodes': open_nodes, 'failed_rules': failed,
                'root_interval': seed, 'proof_hash': self.proof_hash()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--local', type=int)
    ap.add_argument('--audit', action='store_true')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    checker = Verifier(json.loads(args.certificate.read_text()))
    require(not (args.audit and args.local is not None), 'choose audit or a single local rule')
    result = checker.audit() if args.audit else (
        checker.closed() if args.local is None else checker.local(args.local))
    if args.local is not None and not args.audit:
        result['status'] = 'one uniform local cover verified; its dependencies remain obligations'
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    if args.audit:
        print(json.dumps({'verified_rules': len(result['verified_rules']),
                          'open_nodes': len(result['open_nodes']),
                          'failed_rules': len(result['failed_rules'])}, indent=2))
    else:
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
