#!/usr/bin/env python3
"""Exact verifier for cyclic interval types on correlated parameter domains.

Proper extensions, all-n seeds, and closure are mandatory. Box arithmetic is
only used as a sufficient bound in a common chart's base coordinates.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path

from chart_geometry import Domain, compare, relative_box
from explore import state_of
from type_graph_geometry import endpoint, exchange, full_labels, require, root_cells
from verify_cyclic_types import Verifier, contains_box, cover_parameter_box


class ChartVerifier(Verifier):
    def __init__(self, data):
        require(data['format'] == 'freiman-chart-types-v1', 'unknown correlated certificate format')
        self.data, self.nodes = data, data['nodes']
        self.cells = [Domain.read(c) for c in data['cells']]
        self.checked = {}

    def node(self, index):
        require(type(index) is int and 0 <= index < len(self.nodes), 'invalid node index')
        node = self.nodes[index]
        ci = node['cell']
        require(type(ci) is int and 0 <= ci < len(self.cells), 'invalid chart index')
        cell = self.cells[ci]
        a, b = (endpoint(cell.states, node[k]) for k in ('lower', 'upper'))
        require(compare(cell, b, a, strict=True), f'node {index}: width is not uniformly positive')
        hull = [endpoint(cell.states, z) for z in full_labels(cell.parity)]
        require(compare(cell, a, hull[0]) and compare(cell, hull[1], b), 'type escapes its cylinder hull')
        return node, cell, a, b

    def child(self, cell, edge):
        u, v = edge['suffixes']
        child = cell.extend(u, v, edge['high'])
        a, b = (endpoint(cell.states, edge[k], (u, v)) for k in ('lower', 'upper'))
        require(compare(cell, b, a, strict=True), 'child interval has no uniform positive width')
        groups = defaultdict(list)
        dependencies = []
        for dest in edge['destinations']:
            swap = dest['swap']
            require(type(swap) is bool, 'invalid exchange flag')
            _, target, lo, hi = self.node(dest['node'])
            actual = child.exchange() if swap else child
            require((target.states, target.parity, target.high) == (actual.states, actual.parity, actual.high),
                    'wrong child orientation or states')
            for key in ('lower', 'upper'):
                point = endpoint(target.states, exchange(edge[key]) if swap else edge[key])
                require(compare(target, point, lo) and compare(target, hi, point),
                        'offered interval escapes destination type')
            original = target.exchange() if swap else target
            signature = (original.words, tuple(map(state_of, original.base.states)),
                         original.base.parity, original.base.high)
            groups[signature].append(original)
            dependencies.append(dest['node'])
        covered = False
        for group in groups.values():
            image = relative_box(child, group[0])
            if image is None:
                continue
            try:
                cover_parameter_box((image.r, image.s, image.ratio),
                    [(c.base.r, c.base.s, c.base.ratio) for c in group])
            except ValueError:
                continue
            covered = True
            break
        require(covered, 'successor domain is not covered in a common parameter chart')
        return a, b, dependencies

    def local(self, index):
        if index in self.checked:
            return self.checked[index]
        node, cell, low, high = self.node(index)
        require(bool(node.get('children')), f'node {index}: unresolved type')
        current, deps = low, []
        for edge in node['children']:
            a, b, children = self.child(cell, edge)
            require(compare(cell, current, a), f'node {index}: uncovered contact')
            require(compare(cell, b, current, strict=True), f'node {index}: nonprogressing cover')
            current = b
            deps.extend(children)
        require(compare(cell, current, high), f'node {index}: upper endpoint not covered')
        result = dict(node=index, children=len(node['children']), dependencies=sorted(set(deps)))
        self.checked[index] = result
        return result

    def seeds(self):
        roots = self.data['roots']
        require(set(roots) == {'zero', 'positive'}, 'both root families required')
        for name, actual in zip(('zero', 'positive'), root_cells()):
            _, domain, low, high = self.node(roots[name])
            source = Domain(actual, ('', ''), actual.high)
            image = relative_box(source, domain)
            require(image is not None and all(contains_box(a, b) for a, b in zip(
                (domain.base.r, domain.base.s, domain.base.ratio), (image.r, image.s, image.ratio))),
                'initial family escapes initial parameter chart')
            a, b = (endpoint(domain.states, z) for z in full_labels(domain.parity))
            require(compare(domain, a, low) and compare(domain, high, b), 'initial full hull is not covered')
        return list(roots.values())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--audit', action='store_true')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    checker = ChartVerifier(json.loads(args.graph.read_text()))
    result = checker.audit() if args.audit else checker.closed()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: len(v) if isinstance(v, list) else v for k,v in result.items()}))


if __name__ == '__main__':
    main()
