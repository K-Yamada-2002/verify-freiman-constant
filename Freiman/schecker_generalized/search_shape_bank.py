#!/usr/bin/env python3
"""Test learned endpoint shapes, their reflections, and the full hull.

The shapes were extracted from the exact depth-six certificates for n=0,1,2.
This is a finite-horizon discovery procedure, not a proved invariant.
"""
from functools import lru_cache
import argparse
import json
from pathlib import Path
from search_types import Search, merge_float, local_endpoints
from explore import state_of, step

SHAPES=(
    (('1',False,'3',True),('3',True,'2',False)),
    (('1',False,'2',False),('3',True,'3',True)),
    (('1',False,'2',True),('3',True,'1',False)),
    (('1',False,'1',False),('2',True,'3',True)),
)
SHAPES8=SHAPES+(
    (('1',False,'3',True),('2',True,'2',False)),
    (('1',False,'2',False),('2',True,'3',True)),
    (('1',False,'1',True),('2',True,'3',True)),
    (('1',False,'1',False),('1',True,'2',True)),
)


def reflect(label):return label[2:]+label[:2]


class ShapeSearch(Search):
    def __init__(self,ratio_bound=20,shapes=SHAPES,max_step=1):
        super().__init__(1,ratio_bound)
        self.shapes=shapes
        self.max_step=max_step
        self.digit_budget=True
        self.candidates=lru_cache(None)(self._candidates)
        self.options=lru_cache(None)(self._options)

    def children(self,u,v):
        first=list(super().children(u,v))
        seen=set()
        for child in first:
            seen.add(child[:2]);yield child
        if self.max_step==2:
            for uu,vv,offset,scale in first:
                for uuu,vvv,off2,scale2 in super().children(uu,vv):
                    if (uuu,vvv) not in seen:
                        seen.add((uuu,vvv))
                        yield uuu,vvv,offset+scale*off2,scale*scale2

    def _candidates(self,u,v):
        pool=self.pool(u,v);by_label={label:z for z,label in pool}
        lo,hi=self.parameters(u,v)[-2]
        lower=min(pool,key=lambda e:abs(e[0]-lo))
        upper=min(pool,key=lambda e:abs(e[0]-hi))
        out=[(lower[0],upper[0],lower[1],upper[1],'full')]
        for i,(aa,bb) in enumerate(self.shapes,1):
            for reflected in (False,True):
                a,b=(reflect(aa),reflect(bb)) if reflected else (aa,bb)
                if a not in by_label or b not in by_label:continue
                x,y=by_label[a],by_label[b]
                if x>y:x,y,a,b=y,x,b,a
                if x<y:out.append((x,y,a,b,f'J{i}'+('R' if reflected else '')))
        return tuple(out)

    def _options(self,u,v,depth):
        ratio=self.parameters(u,v)[-1]
        if not 1/self.ratio_bound<=ratio<=self.ratio_bound:return ()
        candidates=self.candidates(u,v)
        if depth==0:return candidates[:1]
        offers=[]
        for uu,vv,off,scale in self.children(u,v):
            cost=len(uu)+len(vv)-len(u)-len(v)
            offers.extend((off+scale*a,off+scale*b)
                          for a,b in self.domain(uu,vv,max(0,depth-cost)))
        components=merge_float(offers)
        return tuple(c for c in candidates if any(a-1e-13<=c[0] and c[1]<=b+1e-13
                                                   for a,b in components))

    def _domain(self,u,v,depth):
        self.calls+=1
        return tuple(merge_float((x[0],x[1]) for x in self.options(u,v,depth)))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=8)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--bank',type=int,choices=(4,8),default=4)
    ap.add_argument('--root-only',action='store_true')
    ap.add_argument('--max-step',type=int,choices=(1,2),default=1)
    args=ap.parse_args()
    shapes=SHAPES if args.bank==4 else SHAPES8
    search=ShapeSearch(shapes=shapes,max_step=args.max_step);rows=[]
    roots=[('3211'+'313121'*n+'3','4322'+'313121'*n) for n in range(4)]
    roots += [('321','431'),('32113','4323'),('3131','3131')]
    if args.root_only:roots=roots[:1]
    for u,v in roots:
        for depth in range(1,args.depth+1):
            row=search.describe(u,v,depth)
            row['admitted_shapes']=[c[4] for c in search.options(u,v,depth)]
            rows.append(row)
            print(u,v,depth,row['components'],round(row['width_fraction'],8),row['admitted_shapes'],flush=True)
    result={'status':'finite shape-bank test; NOT a filling certificate',
            'shapes':shapes,'ratio_bound':20,'max_step':args.max_step,
            'horizon_unit':'total appended digits along every path',
            'calls':search.calls,'rows':rows}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
