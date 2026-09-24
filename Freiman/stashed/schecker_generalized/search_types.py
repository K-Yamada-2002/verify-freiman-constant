#!/usr/bin/env python3
"""Discover endpoint types by finite-horizon refinement and inward rounding.

Floating-point discovery only. Endpoints are pairs of explicit admissible
extremal streams after short suffixes. A surviving interval is NOT proved
filled: a uniform invariant certificate is still required.
"""
import argparse
from bisect import bisect_left, bisect_right
from functools import lru_cache
import json
from pathlib import Path
from explore import matrix, state_of, step, extreme_tail, extensions


def value(q):
    return float(q.a)+float(q.b)*(462.0**0.5)


@lru_cache(None)
def tail(state, high):
    return value(extreme_tail(state,high)[0])


@lru_cache(None)
def local_endpoints(state, menu_depth):
    """(value, suffix, tail_maximize) for an explicit legal endpoint stream."""
    out=[]
    for word in extensions(state,menu_depth):
        suffix=word[len(state):]
        a,b,c,d=matrix(suffix)
        for high in (False,True):
            t=tail(state_of(word),high)
            out.append(((a*t+b)/(c*t+d),suffix,high))
    return tuple(sorted(out))


def merge_float(intervals):
    result=[]
    for lo,hi in sorted(intervals):
        if hi<=lo:
            continue
        if result and lo<=result[-1][1]+1e-13:
            result[-1]=(result[-1][0],max(hi,result[-1][1]))
        else:
            result.append((lo,hi))
    return result


class Search:
    def __init__(self,menu_depth=1,ratio_bound=5):
        self.menu_depth=menu_depth
        self.ratio_bound=ratio_bound
        self.calls=0
        self.domain=lru_cache(None)(self._domain)
        self.parameters=lru_cache(None)(self._parameters)
        self.pool=lru_cache(None)(self._pool)

    def _parameters(self,u,v):
        _,_,cu,du=matrix(u);_,_,cv,dv=matrix(v)
        r,s,q=cu/du,cv/dv,(du/dv)**2
        el,er=(-1)**len(u),(-1)**len(v)
        def f(x,y):return el*x/(1+r*x)+q*er*y/(1+s*y)
        l=sorted(el*x/(1+r*x) for x in (tail(state_of(u),False),tail(state_of(u),True)))
        rr=sorted(q*er*x/(1+s*x) for x in (tail(state_of(v),False),tail(state_of(v),True)))
        ratio=(rr[1]-rr[0])/(l[1]-l[0])
        return r,s,q,el,er,(l[0]+rr[0],l[1]+rr[1]),ratio

    def _pool(self,u,v):
        r,s,q,el,er,_,_=self.parameters(u,v)
        entries=[]
        for x,su,hu in local_endpoints(state_of(u),self.menu_depth):
            for y,sv,hv in local_endpoints(state_of(v),self.menu_depth):
                z=el*x/(1+r*x)+q*er*y/(1+s*y)
                entries.append((z,(su,hu,sv,hv)))
        return sorted(entries)

    def children(self,u,v):
        r,s,q,el,er,_,_=self.parameters(u,v)
        for digit in '123':
            a=int(digit)
            if step(state_of(u),digit) is not None:
                # F_parent = offset + scale * F_child.
                yield u+digit,v,el/(a+r),1/(a+r)**2
            if step(state_of(v),digit) is not None:
                yield u,v+digit,q*er/(a+s),1.0

    def _domain(self,u,v,depth):
        self.calls+=1
        *_,hull,ratio=self.parameters(u,v)
        if not 1/self.ratio_bound<=ratio<=self.ratio_bound:
            return ()
        if not depth:
            return (hull,)
        offers=[]
        for uu,vv,offset,scale in self.children(u,v):
            offers.extend((offset+scale*lo,offset+scale*hi)
                          for lo,hi in self.domain(uu,vv,depth-1))
        pool=self.pool(u,v);values=[x[0] for x in pool]
        result=[]
        for lo,hi in merge_float(offers):
            first=bisect_left(values,lo-1e-13)
            last=bisect_right(values,hi+1e-13)-1
            if first<last:
                result.append((values[first],values[last]))
        return tuple(merge_float(result))

    def describe(self,u,v,depth):
        hull=self.parameters(u,v)[-2]
        domain=self.domain(u,v,depth)
        pool=self.pool(u,v)
        def label(x):
            return min(pool,key=lambda row:abs(row[0]-x))[1]
        return {'left':u,'right':v,'depth':depth,'components':len(domain),
                'width_fraction':sum(hi-lo for lo,hi in domain)/(hull[1]-hull[0]),
                'intervals':[{'normalized':[lo,hi], 'lower_type':label(lo),
                              'upper_type':label(hi)} for lo,hi in domain]}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=6)
    ap.add_argument('--menu-depth',type=int,default=1)
    ap.add_argument('--ratio-bound',type=float,default=5)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    search=Search(args.menu_depth,args.ratio_bound)
    roots=[('32113','4322'),('321133','43221'),('3131','3131'),
           ('321','431'),('32113','4323')]
    rows=[]
    for u,v in roots:
        for depth in range(1,args.depth+1):
            row=search.describe(u,v,depth)
            rows.append(row)
            print(u,v,depth,row['components'],round(row['width_fraction'],8),flush=True)
    result={'status':'floating-point finite-horizon discovery; NOT a filling certificate',
            'menu_depth':args.menu_depth,'ratio_bound':args.ratio_bound,
            'calls':search.calls,'rows':rows}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
