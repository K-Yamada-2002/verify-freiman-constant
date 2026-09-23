#!/usr/bin/env python3
"""Independent exact checker for a finite cyclic Freiman interval-type graph.

All reachable types must have a verified cover. A depth cutoff, an open leaf,
or a claimed success flag never substitutes for this requirement.
"""
import argparse
import hashlib
import json
from pathlib import Path

from explore import state_of
from type_graph_geometry import (Cell, endpoint, exchange, full_labels, ge,
                                 require, root_cells, swapped, transition)


def contains_box(outer, inner):
    return outer[0] <= inner[0] <= inner[1] <= outer[1]


def cover_parameter_box(image, boxes):
    """Exact coverage by a finite union of closed product boxes.

    Sweep the first coordinate at all box boundaries and recurse on each
    resulting closed slab. Degenerate coordinates are checked as points.
    No inference from just the corners or intersecting boxes is made.
    """
    require(bool(boxes), 'missing parameter destinations')
    if not image:
        return
    low, high = image[0]
    boxes = [b for b in boxes if b[0][0] <= high and low <= b[0][1]]
    require(bool(boxes), 'uncovered parameter box')
    cuts = sorted({low, high} | {x for b in boxes for x in b[0] if low < x < high})
    slabs = list(zip(cuts, cuts[1:])) if low != high else [(low, high)]
    for left, right in slabs:
        active = [b[1:] for b in boxes if b[0][0] <= left and right <= b[0][1]]
        require(bool(active), 'gap in destination parameter boxes')
        cover_parameter_box(image[1:], active)


class Verifier:
    def __init__(self, data):
        require(data['format'] == 'freiman-cyclic-types-v1', 'unknown certificate format')
        self.data = data
        self.cells = [Cell.read(c) for c in data['cells']]
        self.nodes = data['nodes']
        self.checked = {}

    def node(self, index):
        require(type(index) is int and 0 <= index < len(self.nodes), 'invalid node index')
        node = self.nodes[index]
        ci = node['cell']
        require(type(ci) is int and 0 <= ci < len(self.cells), 'invalid cell index')
        cell = self.cells[ci]
        a, b = (endpoint(cell.states, node[k]) for k in ('lower', 'upper'))
        require(ge(cell, b, a, strict=True), f'node {index}: width is not uniformly positive')
        hull = [endpoint(cell.states, z) for z in full_labels(cell.parity)]
        require(ge(cell, a, hull[0]) and ge(cell, hull[1], b), 'type escapes its cylinder hull')
        return node, cell, a, b

    @staticmethod
    def cover_ratio(image, boxes):
        current, end = image
        require(bool(boxes), 'missing parameter destinations')
        for low, high in sorted(boxes):
            if high < current:
                continue
            require(low <= current, 'gap in destination ratio domains')
            current = max(current, high)
            if current >= end:
                return
        require(current >= end, 'successor ratio escapes the destination domains')

    def child(self, cell, edge):
        u, v = edge['suffixes']
        child = transition(cell, u, v, edge['high'])
        a, b = (endpoint(cell.states, edge[k], (u, v)) for k in ('lower', 'upper'))
        require(ge(cell, b, a, strict=True), 'child interval has no uniform positive width')
        coverage = []
        dependencies = []
        for dest in edge['destinations']:
            swap = dest['swap']
            require(type(swap) is bool, 'invalid exchange flag')
            target, tc, lo, hi = self.node(dest['node'])
            image = swapped(child) if swap else child
            require(tuple(map(state_of, tc.states)) == image.states, 'wrong child states')
            require(tc.parity == image.parity and tc.high == image.high, 'wrong child orientation or anchors')
            for key in ('lower', 'upper'):
                label = exchange(edge[key]) if swap else edge[key]
                point = endpoint(tc.states, label)
                require(ge(tc, point, lo) and ge(tc, hi, point),
                        'offered interval escapes destination type')
            # Bring every destination back to the parent's unswapped child
            # coordinates, then verify the entire three-dimensional union.
            original = swapped(tc) if swap else tc
            coverage.append((original.r, original.s, original.ratio))
            dependencies.append(dest['node'])
        cover_parameter_box((child.r, child.s, child.ratio), coverage)
        return a, b, dependencies

    def local(self, index):
        if index in self.checked:
            return self.checked[index]
        node, cell, low, high = self.node(index)
        require(bool(node.get('children')), f'node {index}: unresolved type')
        current, dependencies = low, []
        for edge in node['children']:
            a, b, deps = self.child(cell, edge)
            require(ge(cell, current, a), f'node {index}: uncovered contact')
            require(ge(cell, b, current, strict=True), f'node {index}: nonprogressing cover')
            current = b
            dependencies.extend(deps)
        require(ge(cell, current, high), f'node {index}: upper endpoint not covered')
        result = dict(node=index, children=len(node['children']), dependencies=sorted(set(dependencies)))
        self.checked[index] = result
        return result

    def seeds(self):
        roots = self.data['roots']
        require(set(roots) == {'zero', 'positive'}, 'both n=0 and all n>=1 are required')
        for name, actual in zip(('zero', 'positive'), root_cells()):
            _, cell, low, high = self.node(roots[name])
            require(tuple(map(state_of, cell.states)) == actual.states and
                    cell.parity == actual.parity and cell.high == actual.high, 'wrong initial type')
            require(all(contains_box(a, b) for a, b in zip(
                (cell.r, cell.s, cell.ratio), (actual.r, actual.s, actual.ratio))),
                'initial family escapes initial type domain')
            a, b = (endpoint(cell.states, z) for z in full_labels(cell.parity))
            require(ge(cell, a, low) and ge(cell, high, b), 'initial full hull is not covered')
        return list(roots.values())

    def closed(self):
        pending = self.seeds()
        reached = set()
        while pending:
            index = pending.pop()
            if index in reached:
                continue
            reached.add(index)
            pending.extend(self.local(index)['dependencies'])
        return dict(status='all A_n full hulls verified by a closed cyclic graph',
                    verified_nodes=len(reached), proof_hash=self.proof_hash())

    def audit(self):
        self.seeds()
        verified, failed, opened = [], [], []
        for i, node in enumerate(self.nodes):
            if not node.get('children'):
                opened.append(i)
                continue
            try:
                verified.append(self.local(i))
            except ValueError as error:
                failed.append(dict(node=i, error=str(error)))
        return dict(status='local audit only; no infinite filling assertion',
                    verified_rules=verified, open_nodes=opened, failed_rules=failed,
                    proof_hash=self.proof_hash())

    def proof_hash(self):
        return hashlib.sha256(json.dumps({k: self.data[k] for k in
            ('format', 'cells', 'nodes', 'roots')}, sort_keys=True,
            separators=(',', ':')).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--audit', action='store_true')
    parser.add_argument('--local', type=int)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(not (args.audit and args.local is not None), 'choose audit or local')
    checker = Verifier(json.loads(args.certificate.read_text()))
    result = checker.audit() if args.audit else (checker.closed() if args.local is None
                                               else checker.local(args.local))
    if args.local is not None:
        result['status'] = 'one local rule verified; dependencies remain obligations'
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: len(v) if isinstance(v, list) else v for k, v in result.items()}, indent=2))


if __name__ == '__main__':
    main()
