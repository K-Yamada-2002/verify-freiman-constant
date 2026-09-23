#!/usr/bin/env python3
"""Exact backward reachability of parameter points witnessing a type gap.

Exclusion concerns the selected partial strategy. A surviving path is not a
gap in A_n: different children can cover the same target value. Reaching the
positive root box alone does not imply reaching an actual integer n.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

from cyclic_frontier_gaps import verify_witness
from explore import Q, matrix
from type_graph_geometry import Cell, decode, encode, parameters, require, root_cells, swapped, transition
from verify_cyclic_types import Verifier


def inside(point, cell):
    return all(lo <= x <= hi for x, (lo, hi) in zip(point, (cell.r, cell.s, cell.ratio)))


def inverse_shape(word, value):
    a, b, c, d = matrix(word)
    denominator = b*value-a
    return None if denominator == 0 else (c-d*value)/denominator


def preimage(parent, edge, swap, point):
    """Unique finite preimage, or None if it misses the parent domain."""
    r, s, ratio = point
    if swap:
        r, s, ratio = s, r, 1/ratio
    u, v = edge['suffixes']
    r, s = inverse_shape(u, r), inverse_shape(v, s)
    if r is None or s is None:
        return None
    if not (parent.r[0] <= r <= parent.r[1] and parent.s[0] <= s <= parent.s[1]):
        return None
    unit = Cell(parent.states, parent.parity, parent.high, (r, r), (s, s), (Q(1), Q(1)))
    image = transition(unit, u, v, edge['high'])
    require(image.ratio[0] == image.ratio[1], 'point image has nonzero width')
    ratio /= image.ratio[0]
    if not parent.ratio[0] <= ratio <= parent.ratio[1]:
        return None
    return r, s, ratio


class BackwardAudit:
    def __init__(self, checker):
        self.checker = checker
        self.incoming = defaultdict(list)
        for i, node in enumerate(checker.nodes):
            for j, edge in enumerate(node.get('children', [])):
                for k, dest in enumerate(edge['destinations']):
                    self.incoming[dest['node']].append((i, j, k))
        self.seeds = defaultdict(list)
        for name, cell in zip(('zero', 'positive'), root_cells()):
            self.seeds[checker.data['roots'][name]].append((name, cell))
        first_positive = parameters('3211'+'313121'+'3', '4322'+'313121')
        self.first_positive = tuple(b[0] for b in (first_positive.r, first_positive.s, first_positive.ratio))

    def trace(self, index, point, depth, ancestors=frozenset()):
        require(depth >= 0, 'negative backward depth')
        cell = self.checker.cells[self.checker.nodes[index]['cell']]
        require(inside(point, cell), 'point outside node domain')
        row = dict(node=index, point=list(map(encode, point)))
        for name, seed in self.seeds[index]:
            if inside(point, seed):
                status = ('reachable_from_n0' if name == 'zero' else
                          'reachable_from_n1' if point == self.first_positive else 'possible_from_positive_box')
                return dict(row, status=status, seed=name)
        key = index, point
        if key in ancestors:
            return dict(row, status='inconclusive_cycle')
        if depth == 0:
            return dict(row, status='inconclusive_depth')
        parents = []
        for i, j, k in self.incoming[index]:
            node = self.checker.nodes[i]
            edge = node['children'][j]
            parent = self.checker.cells[node['cell']]
            previous = preimage(parent, edge, edge['destinations'][k]['swap'], point)
            branch = dict(parent=i, edge=j, destination=k)
            if previous is None:
                branch['status'] = 'outside_parent_domain'
            else:
                child = self.trace(i, previous, depth-1, ancestors | {key})
                branch.update(status=child['status'], trace=child)
            parents.append(branch)
        statuses = {p['status'] for p in parents}
        status = next((s for s in ('reachable_from_n0', 'reachable_from_n1', 'possible_from_positive_box',
                                  'inconclusive_cycle', 'inconclusive_depth') if s in statuses), 'excluded')
        return dict(row, status=status, parents=parents)

    def witness(self, witness, depth):
        verify_witness(self.checker, witness)
        return self.trace(witness['node'], tuple(map(decode, witness['parameters'])), depth)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('gaps', type=Path)
    ap.add_argument('--depth', type=int, default=6)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--verify', action='store_true')
    args = ap.parse_args()
    checker = Verifier(json.loads(args.graph.read_text()))
    gaps = json.loads(args.gaps.read_text())
    require(gaps['source_proof_hash'] == checker.proof_hash(), 'gap source differs from graph')
    checker.seeds()
    audit = checker.audit()
    require(not audit['failed_rules'], 'source has invalid local rules')
    backward = BackwardAudit(checker)
    traces = []
    for witness in gaps['witnesses']:
        traces.append(backward.witness(witness, args.depth))
    result = dict(status='exact parameter reachability audit of a selected strategy; no full filling claim',
                  source_proof_hash=checker.proof_hash(), depth=args.depth,
                  counts=dict(Counter(t['status'] for t in traces)), traces=traces)
    if args.verify:
        require(json.loads(args.output.read_text()) == result, 'backward certificate differs on replay')
    else:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['counts']), flush=True)


if __name__ == '__main__':
    main()
