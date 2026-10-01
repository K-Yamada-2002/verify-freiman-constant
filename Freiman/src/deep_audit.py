"""Fast exhaustive numerical screening, then exact certificates for any gap.

Gap verification is O(number_of_left_cylinders * log(number_of_right_cylinders))
using sorted disjoint right cylinder intervals; all comparisons are exact.
"""
import argparse
import json
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
import numpy as np
from exact_cf import K, CF, cf, interval, side_endpoint, parameters, matrix
from menu_search import extensions, branch
from obstruction_probe import scan


def streaming_gap(a,b,depth,chunk=96):
    r,s,rho=map(float,parameters(a,b))
    aa=np.array([branch(r,len(a)%2,e)[0] for e in extensions(scan(a),depth)])
    bb=np.array([branch(s,len(b)%2,e)[0] for e in extensions(scan(b),depth)])
    pieces=[]
    for start in range(0,len(aa),chunk):
        rows=aa[start:start+chunk]
        lo=(rows[:,None,0]+rho*bb[None,:,0]).ravel()
        hi=(rows[:,None,1]+rho*bb[None,:,1]).ravel()
        order=np.argsort(lo);lo=lo[order];upper=np.maximum.accumulate(hi[order])
        breaks=np.flatnonzero(lo[1:]>upper[:-1]+1e-13)
        begins=np.r_[0,breaks+1];ends=np.r_[breaks,len(lo)-1]
        pieces.extend(zip(lo[begins],upper[ends]))
    merged=[]
    for lo,hi in sorted(pieces):
        if merged and lo<=merged[-1][1]+1e-13:
            merged[-1]=(merged[-1][0],max(merged[-1][1],hi))
        else:merged.append((lo,hi))
    if len(merged)<2:return None
    norm=Q(str((merged[0][1]+merged[1][0])/2))
    _,ap,_,aq=matrix(a);_,bp,_,bq=matrix(b)
    return K(Q(ap,aq)+Q(bp,bq)+norm/(aq*aq))


def numerical_gap(a,b,depth):
    r,s,rho=map(float,parameters(a,b))
    ea=extensions(scan(a),depth);eb=extensions(scan(b),depth)
    aa=np.array([branch(r,len(a)%2,e)[0] for e in ea])
    bb=np.array([branch(s,len(b)%2,e)[0] for e in eb])
    lo=(aa[:,None,0]+rho*bb[None,:,0]).ravel()
    hi=(aa[:,None,1]+rho*bb[None,:,1]).ravel()
    order=np.argsort(lo)
    sorted_lo=lo[order];sorted_hi=hi[order]
    upper=np.maximum.accumulate(sorted_hi)
    gaps=np.flatnonzero(sorted_lo[1:]>upper[:-1]+1e-13)
    if not len(gaps):return None
    i=int(gaps[0]);previous=int(np.argmax(sorted_hi[:i+1]))
    li,lj=divmod(int(order[previous]),len(eb))
    ri,rj=divmod(int(order[i+1]),len(eb))
    low=interval(a+ea[li][0],b+eb[lj][0])[1]
    high=interval(a+ea[ri][0],b+eb[rj][0])[0]
    return (low+high)/2 if low<high else None


def exact_gap_around(a,b,depth,target):
    left=sorted((side_endpoint(a+e[0],True),side_endpoint(a+e[0],False))
                for e in extensions(scan(a),depth))
    right=sorted((side_endpoint(b+e[0],True),side_endpoint(b+e[0],False))
                 for e in extensions(scan(b),depth))
    assert all(x[1]<y[0] for x,y in zip(right,right[1:]))
    lower,upper=interval(a,b)
    if not lower<target<upper:return None
    for lo,hi in left:
        start,stop=0,len(right)
        while start<stop:
            mid=(start+stop)//2
            if hi+right[mid][1]<target:start=mid+1
            else:stop=mid
        cut=start
        if cut<len(right):
            if lo+right[cut][0]<=target:return None
            upper=min(upper,lo+right[cut][0])
        if cut:lower=max(lower,hi+right[cut-1][1])
    assert lower<target<upper
    return lower,upper


def audit_root(a,b,max_depth=7):
    for depth in range(1,max_depth+1):
        target=numerical_gap(a,b,depth)
        if target is not None:
            gap=exact_gap_around(a,b,depth,target)
            if gap:
                return {'status':'certified_intrinsic_gap','depth':depth,
                        'gap':[v.data() for v in gap],
                        'gap_decimal':[float(v) for v in gap]}
            return {'status':'numerical_signal_not_certified','depth':depth}
    return {'status':'no_gap_detected_through_depth','depth':max_depth}


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--inventory',nargs='+',default=['root_inventory_depth11.json','root_inventory_center3.json'])
    p.add_argument('--depth',type=int,default=7)
    p.add_argument('--output',default='root_deep_audit.json')
    args=p.parse_args();base=DATA
    roots={}
    for name in args.inventory:
        for root in json.loads((base/name).read_text())['selected_roots']:
            roots[(root['a'],root['b'],root['center'])]=root
    records=[]
    for (a,b,center),root in roots.items():
        result={'a':a,'b':b,'center':center,**audit_root(tuple(map(int,a)),tuple(map(int,b)),args.depth)}
        records.append(result);print(json.dumps(result),flush=True)
    (base/args.output).write_text(json.dumps({'proof_complete':False,'records':records},indent=2)+'\n')
