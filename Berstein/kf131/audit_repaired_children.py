#!/usr/bin/env python3
"""Look for exact obstructions in new obligations; absence is inconclusive."""
import argparse
import hashlib
import json
from pathlib import Path

from exact import state_of
from scalar_obstructions import discover, rational_in, replay
from verify_scalar_graph import ScalarVerifier


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--budget',type=int,default=1500)
    ap.add_argument('--limit',type=int,default=100000)
    args = ap.parse_args()
    raw = args.graph.read_bytes()
    data = json.loads(raw)
    checker = ScalarVerifier(data)
    result = dict(source_sha256=hashlib.sha256(raw).hexdigest(),obstructions=[],
                  unresolved=[],budget_per_point=args.budget,
                  scope='five points at one interior parameter per open type; not a filling proof')
    count = 0
    for j,node in enumerate(data['nodes']):
        if node['covered'] or count >= args.limit:
            continue
        count += 1
        params = tuple(rational_in(box) for box in checker.box(j))
        a,b = checker.interval(node['interval'])
        for t in (a,b,(a+b)/2,(3*a+b)/4,(a+3*b)/4):
            tree = discover(tuple(map(state_of,node['states'])),node['parity'],params,t,args.budget)
            if tree is None:
                continue
            cert = dict(source_node=node.get('source_node',j),graph_node=j,
                        type={k:v for k,v in node.items() if k not in ('children','covered','id')},
                        settings=data['settings'],parameters=list(map(str,params)),target=str(t),tree=tree)
            cert['verification'] = replay(cert)
            result['obstructions'].append(cert)
            break
        else:
            result['unresolved'].append(j)
        if count % 10 == 0:
            print(json.dumps(dict(checked=count,excluded=len(result['obstructions']))),flush=True)
            args.output.write_text(json.dumps(result,indent=2)+'\n')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(checked=count,excluded=len(result['obstructions']),
                         unresolved=len(result['unresolved']))),flush=True)


if __name__ == '__main__':
    main()
