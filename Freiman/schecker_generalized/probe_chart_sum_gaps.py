#!/usr/bin/env python3
"""Bounded-depth gap search using the compressed interval-sum discovery.

All accepted witnesses are replayed using the unchanged exact cylinder-sum
verifier. No-gap at any finite depth is not a positive filling certificate.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import time
from audit_chart_gaps import point_checker
from cyclic_frontier_gaps import numeric_gaps,value,verify_witness,samples
from explore import Q
from search_cyclic_types import fl
from type_graph_geometry import encode
from verify_piecewise_charts import PiecewiseVerifier


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path);ap.add_argument('--node',type=int,required=True)
    ap.add_argument('--depths',type=int,nargs='+',default=[7,8,9]);ap.add_argument('--corners',action='store_true')
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if min(args.depths)<1:ap.error('positive depths required')
    checker=PiecewiseVerifier(json.loads(args.graph.read_text()))
    _,domain,_,_=checker.node(args.node)
    result=dict(source_proof_hash=checker.proof_hash(),node=args.node,rows=[],witnesses=[],
                status='finite gap discovery only; no positive filling assertion')
    for point in samples(domain.base,args.corners):
        local=point_checker(checker,args.node,point);_,cell,lo,hi=local.node(0)
        pars=tuple(a for a,b in (cell.r,cell.s,cell.ratio))
        target=tuple(fl(value(cell,pars,z)) for z in (lo,hi))
        for depth in args.depths:
            start=time.monotonic();gaps=list(numeric_gaps(cell,pars,depth,target))
            row=dict(depth=depth,seconds=time.monotonic()-start,base_parameters=list(map(encode,point)),candidates=gaps)
            result['rows'].append(row);print(json.dumps(row),flush=True)
            for a,b in gaps:
                witness=dict(node=0,depth=depth,parameters=list(map(encode,pars)),
                             gap=list(map(encode,(Q(F(str((2*a+b)/3))),Q(F(str((a+2*b)/3)))))))
                try:verification=verify_witness(local,witness)
                except ValueError:continue
                result['witnesses'].append(dict(node=args.node,base_parameters=list(map(encode,point)),
                                                witness=witness,exact_replay=verification))
                print('EXACT WITNESS '+json.dumps(verification),flush=True);break
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            if result['witnesses']:return

if __name__=='__main__':main()
