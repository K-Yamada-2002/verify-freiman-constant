#!/usr/bin/env python3
"""Exact chart induction with parameter-dependent local cover choices.

Parameter pieces are inline guards, not zero-digit induction edges. Every
dependency still appends a nonempty legal word pair, preserving contraction.
"""
import argparse
import json
from pathlib import Path

from chart_geometry import Domain, compare
from type_graph_geometry import endpoint, require
from verify_chart_types import ChartVerifier
from verify_cyclic_types import contains_box, cover_parameter_box


FORMAT = 'freiman-piecewise-chart-types-v1'


class PiecewiseVerifier(ChartVerifier):
    def __init__(self, data):
        require(data['format'] == FORMAT, 'unknown piecewise certificate format')
        self.data, self.nodes = data, data['nodes']
        self.cells = [Domain.read(c) for c in data['cells']]
        self.checked = {}

    def local(self, index):
        if index in self.checked:
            return self.checked[index]
        node = self.nodes[index]
        if not node.get('pieces'):
            return super().local(index)
        require(not node.get('children'), 'ambiguous guarded and unguarded rule')
        _, domain, lower, upper = self.node(index)
        boxes, deps, count = [], [], 0
        for piece in node['pieces']:
            cid = piece['cell']
            require(type(cid) is int and 0 <= cid < len(self.cells), 'invalid piece domain')
            part = self.cells[cid]
            require((part.words, part.high, part.base.states, part.base.parity, part.base.high) ==
                    (domain.words, domain.high, domain.base.states, domain.base.parity, domain.base.high),
                    'parameter piece uses a different chart')
            box = (part.base.r, part.base.s, part.base.ratio)
            require(all(contains_box(a,b) for a,b in zip(
                (domain.base.r, domain.base.s, domain.base.ratio), box)), 'piece escapes parent domain')
            boxes.append(box)
            require(bool(piece.get('children')), 'unresolved parameter piece')
            current = lower
            for edge in piece['children']:
                a,b,children = self.child(part, edge)
                require(compare(part, current, a), 'uncovered contact in parameter piece')
                require(compare(part, b, current, strict=True), 'nonprogressing parameter piece')
                current = b
                deps.extend(children)
                count += 1
            require(compare(part, current, upper), 'piece fails to cover whole target interval')
        cover_parameter_box((domain.base.r, domain.base.s, domain.base.ratio), boxes)
        result = dict(node=index, children=count, parameter_pieces=len(boxes), dependencies=sorted(set(deps)))
        self.checked[index] = result
        return result

    def audit(self):
        self.seeds()
        verified, failed, opened = [], [], []
        for i,node in enumerate(self.nodes):
            if not node.get('children') and not node.get('pieces'):
                opened.append(i)
                continue
            try:
                verified.append(self.local(i))
            except ValueError as error:
                failed.append(dict(node=i, error=str(error)))
        return dict(status='local audit only; no infinite filling assertion', verified_rules=verified,
                    failed_rules=failed, open_nodes=opened, proof_hash=self.proof_hash())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--audit', action='store_true')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    checker = PiecewiseVerifier(json.loads(args.graph.read_text()))
    result = checker.audit() if args.audit else checker.closed()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in result.items()}))


if __name__ == '__main__':
    main()
