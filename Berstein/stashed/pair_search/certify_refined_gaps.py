#!/usr/bin/env python3
"""Independently exclude closed subintervals of gaps, using only Fraction.

The DFS partitions the full Cartesian product into legal cylinder pairs.
Every terminal pair is strictly disjoint from the proposed closed interval.
No floating point or C++ cover output is trusted as an exclusion certificate.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from search import Model
ROOT=Path(__file__).resolve().parent

def exclude(model,left,right,lo,hi,budget=2000000):
    # Universal tails suffice: no state-extrema computation from the C++
    # preparation is reused in this independent exclusion.
    bounds={s:(Q(1,4),Q(4,5)) for s in model.states}
    stack=[(model.cylinder(u,bounds),model.cylinder(v,bounds)) for u in left for v in right]
    visited=leaves=0;maxdepth=0;digest=hashlib.sha256()
    while stack:
        if visited>=budget:raise RuntimeError('Exclusion budget exhausted')
        x,y=stack.pop();visited+=1
        a,b=x[3]+y[3],x[4]+y[4]
        if b<lo or a>hi:
            leaves+=1;maxdepth=max(maxdepth,len(x[0]),len(y[0]))
            digest.update(f'{x[0]} {y[0]} {a} {b}\n'.encode())
        elif x[4]-x[3]>=y[4]-y[3]:stack.extend((z,y) for z in model.children(x,bounds))
        else:stack.extend((x,z) for z in model.children(y,bounds))
    return dict(visited=visited,excluded_leaves=leaves,max_depth=maxdepth,leaf_sha256=digest.hexdigest())

def gaps(claim):
    lo,hi=map(Q,claim['target_sum']);end=lo;out=[]
    for a,b in claim['covered']:
        a,b=Q(a,claim['scale']),Q(b,claim['scale'])
        if a>end:out.append((end,a))
        end=max(end,b)
    if end<hi:out.append((end,hi))
    return out

def main():
    data=json.loads((ROOT/'refined_1e8.json').read_text())
    source=json.loads((ROOT/'reduced_ten.json').read_text())
    defs={d['graph']:d for d in json.loads((ROOT/'reduced_ten_audit.json').read_text())['definitions']}
    output=[]
    for claim in data['claims']:
        if not claim['complete']:raise ValueError('Incomplete scan')
        gs=gaps(claim)
        if not gs:continue
        c=source['claims'][claim['claim']-1];d=defs[c['graph']]
        m=Model(d['label'],d['alphabet'],d['forbidden'])
        for a,b in gs:
            lo,hi=(3*a+b)/4,(a+3*b)/4
            result=exclude(m,c['left'],c['right'],lo,hi)
            result.update(claim=claim['claim'],excluded_closed_interval=[str(lo),str(hi)],
                          decimal_display=[float(lo),float(hi)],midpoint=str((a+b)/2))
            output.append(result)
            print(claim['claim'],result['decimal_display'],result['visited'],flush=True)
            (ROOT/'refined_gap_certificates.json').write_text(json.dumps(output,indent=2)+'\n')
if __name__=='__main__':main()
