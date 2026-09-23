#!/usr/bin/env python3
"""Replay one uniform contact that a marginal parameter box cannot prove."""
import argparse
from itertools import product
import json
from pathlib import Path

from chart_geometry import Domain, compare, relative_box
from cyclic_frontier_gaps import value
from type_graph_geometry import Cell, anchor, decode, encode, endpoint, ge, require
from verify_chart_types import ChartVerifier


def verify_example(record):
    domain = Domain.read(record['domain'])
    first, second = (tuple(map(decode, record[k])) for k in ('first', 'second'))
    for point in (first, second):
        require(all(anchor(s, False) <= x <= anchor(s, True) for s,x in zip(domain.states, point)),
                'contact endpoint outside legal tail hull')
    require(compare(domain, first, second), 'contact fails on correlated domain')
    require(not ge(domain.outer, first, second), 'box also proves contact')
    point = tuple(map(decode, record['spurious_parameters']))
    outer = domain.outer
    require(all(a <= x <= b for (a,b),x in zip((outer.r, outer.s, outer.ratio), point)),
            'counterexample outside marginal box')
    require(value(outer, point, first) < value(outer, point, second), 'box counterexample is not strict')
    singleton = Cell(domain.states, domain.parity, domain.high, *((x,x) for x in point))
    pulled = relative_box(Domain(singleton, ('',''), domain.high), domain)
    require(pulled is None or any(not (a <= c <= d <= b) for (a,b),(c,d) in zip(
        (domain.base.r, domain.base.s, domain.base.ratio), (pulled.r, pulled.s, pulled.ratio))),
        'spurious counterexample belongs to the correlated domain')
    return dict(status='uniform contact verified; strict box counterexample excluded from chart')


def build_example(data, index, edge_index):
    checker = ChartVerifier(data)
    checker.local(index)
    node, domain, lower, _ = checker.node(index)
    edge = node['children'][edge_index]
    previous = node['children'][edge_index-1] if edge_index else None
    first = endpoint(domain.states, previous['upper'], previous['suffixes']) if previous else lower
    second = endpoint(domain.states, edge['lower'], edge['suffixes'])
    outer = domain.outer
    point = next(p for p in product(outer.r, outer.s, outer.ratio)
                 if value(outer, p, first) < value(outer, p, second))
    record = dict(source_proof_hash=checker.proof_hash(), node=index, edge=edge_index,
                  domain=domain.record(), first=list(map(encode, first)), second=list(map(encode, second)),
                  spurious_parameters=list(map(encode, point)))
    record.update(verify_example(record))
    return record


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--graph', type=Path)
    ap.add_argument('--node', type=int)
    ap.add_argument('--edge', type=int, default=0)
    ap.add_argument('--verify', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    if args.verify:
        result = verify_example(json.loads(args.verify.read_text()))
    else:
        if args.graph is None or args.node is None or args.output is None:
            ap.error('creation requires --graph, --node and --output')
        result = build_example(json.loads(args.graph.read_text()), args.node, args.edge)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status=result['status'])))


if __name__ == '__main__':
    main()
