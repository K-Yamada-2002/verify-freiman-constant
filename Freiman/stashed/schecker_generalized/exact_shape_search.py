#!/usr/bin/env python3
"""Exact exhaustive finite-horizon viability for a fixed endpoint-shape bank.

Non-survival excludes this bank/ratio bound/one-digit transition rule only.
Survival does not prove any infinite filling assertion.
"""
from functools import lru_cache
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
from explore import hull, restricted_ratio, state_of, step, merge, interval_record
from type_certificates import endpoint
from search_shape_bank import SHAPES, SHAPES8, reflect


class ExactSearch:
    def __init__(self,shapes=SHAPES,bound=20):
        self.shapes=shapes;self.bound=F(bound);self.calls=0
        self.domain=lru_cache(None)(self._domain)
        self.candidates=lru_cache(None)(self._candidates)
        self.endpoint=lru_cache(None)(endpoint)

    def _candidates(self,u,v):
        out=[hull(u,v)]
        for aa,bb in self.shapes:
            for flip in (False,True):
                a,b=(reflect(aa),reflect(bb)) if flip else (aa,bb)
                if any(step(state_of(w),lab[i]) is None
                       for lab in (a,b) for i,w in ((0,u),(2,v))):continue
                x,y=self.endpoint(u,v,a),self.endpoint(u,v,b)
                if x!=y:out.append((min(x,y),max(x,y)))
        return tuple(out)

    def _domain(self,u,v,depth):
        self.calls+=1
        ratio=restricted_ratio(u,v)
        if ratio<1/self.bound or ratio>self.bound:return ()
        if depth==0:return (hull(u,v),)
        offers=[]
        for digit in '123':
            if step(state_of(u),digit) is not None:
                offers.extend(self.domain(u+digit,v,depth-1))
            if step(state_of(v),digit) is not None:
                offers.extend(self.domain(u,v+digit,depth-1))
        components=merge(offers)
        passed=[(lo,hi) for lo,hi in self.candidates(u,v)
                if any(a<=lo and hi<=b for a,b in components)]
        return tuple(merge(passed))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=7)
    ap.add_argument('--bank',type=int,choices=(4,8),default=4)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    search=ExactSearch(SHAPES if args.bank==4 else SHAPES8)
    u,v='32113','4322';rows=[]
    for depth in range(1,args.depth+1):
        domain=search.domain(u,v,depth)
        row={'depth':depth,'components':[interval_record(i) for i in domain],
             'full_hull_survives':domain==(hull(u,v),)}
        rows.append(row)
        print(depth,'components',len(domain),'full',row['full_hull_survives'],'calls',search.calls,flush=True)
    result={'status':'EXACT exhaustive finite-horizon check; no infinite filling assertion',
            'bank_size':args.bank,'ratio_bound':20,'left':u,'right':v,
            'transition':'one appended digit on exactly one side',
            'calls':search.calls,'rows':rows}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
