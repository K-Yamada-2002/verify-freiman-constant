#!/usr/bin/env python3
"""Finite expansion ranks, following Berstein/kf131/closure_diagnostics.py.

This graph has one chosen rule per node; guarded pieces are all required.
Rank is shortest dependency distance to an open node, not distance to proof.
None denotes a structurally closed component, still requiring exact audit.
"""
import argparse
from collections import Counter, deque
import json
from pathlib import Path

from reduce_chart_frontier import dependencies
from verify_piecewise_charts import PiecewiseVerifier


def ranks(data):
    children=dependencies(data)
    parents=[set() for _ in children]
    depth=[None]*len(children)
    queue=deque()
    for i,node in enumerate(data['nodes']):
        for child in children[i]:
            parents[child].add(i)
        if not node.get('children') and not node.get('pieces'):
            depth[i]=0;queue.append(i)
    while queue:
        child=queue.popleft()
        for parent in parents[child]:
            if depth[parent] is None:
                depth[parent]=depth[child]+1;queue.append(parent)
    return depth


def report(data):
    depth=ranks(data)
    return dict(scope='chosen strategy only; finite rank does not refute filledness',
                proof_hash=PiecewiseVerifier(data).proof_hash(),nodes=len(depth),
                root_ranks={k:depth[i] for k,i in data['roots'].items()},
                histogram=dict(sorted(Counter(x for x in depth if x is not None).items())),
                structurally_closed=sum(x is None for x in depth))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graphs',nargs='+',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    results={str(p):report(json.loads(p.read_text())) for p in args.graphs}
    args.output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results),flush=True)


if __name__=='__main__':
    main()
