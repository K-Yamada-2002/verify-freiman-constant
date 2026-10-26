"""Use actual persistent-cylinder width ratio instead of denominator ratio.

The parent full hull normalizes to [0,1+R]. Its r,s dependence is retained in
the child shapes. Transition bounds exploit cancellation before bounding.
"""
import argparse
import json
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
from functools import lru_cache
from exact_cf import parameters
from obstruction_probe import scan
from typed_intervals import E,endpoints
from typed_boxes import Uniform,side_pairs
from typed_catalog import Catalog
from box_certificates import child_box,contains


def phi(r,x):return x/(1+r*x)


def width(state,r):
    m,M=endpoints(state,'base');return phi(r,M)-phi(r,m)


@lru_cache(maxsize=20000)
def normalized_difference_range(state,x,y,bounds):
    m,M=endpoints(state,'base');lo,hi=bounds
    factor=(x-y)/(M-m)
    if factor==0:return E.cast(0),E.cast(0)
    def value(r):return factor*((1+r*m)/(1+r*x))*((1+r*M)/(1+r*y))
    # Derivative of ((1+r*m)(1+r*M))/((1+r*x)(1+r*y)).
    S,P=m+M,m*M;T,V=x+y,x*y
    A,B,C=S-T,2*(P-V),P*T-V*S
    bern=(A+B*lo+C*lo*lo,
          A+B*lo+C*lo*lo+(hi-lo)*(B+2*C*lo)/2,
          A+B*hi+C*hi*hi)
    if all(v>=0 for v in bern) or all(v<=0 for v in bern):
        vals=[value(lo),value(hi)];return min(vals),max(vals)
    # A product enclosure remains rigorous when the derivative changes sign.
    left=[(1+r*m)/(1+r*x) for r in bounds]
    right=[(1+r*M)/(1+r*y) for r in bounds]
    vals=[factor*a*b for a in left for b in right]
    return min(vals),max(vals)


class WidthUniform(Uniform):
    def ge(self,x,y):
        key=x,y
        if key not in self.cache:
            self.checks+=1
            aa=normalized_difference_range(scan(self.a),x[0],y[0],self.box[0])
            bb=normalized_difference_range(scan(self.b),x[1],y[1],self.box[1])
            self.cache[key]=(min((-1)**len(self.a)*a for a in aa)
                            +min(R*(-1)**len(self.b)*b for R in self.box[2] for b in bb))>=0
        return self.cache[key]


class WidthCatalog(Catalog):
    def coordinates(self,a,b):
        r,s,rho=parameters(a,b)
        return r,s,rho*width(scan(b),s)/width(scan(a),r)
    def search_params(self,key,box):
        a,b=self.prototype(key);r,s,R=tuple((lo+hi)/2 for lo,hi in box)
        rho=R*width(scan(a),r)/width(scan(b),s)
        return r,s,rho
    def uniform(self,key):
        a,b=self.prototype(key);return WidthUniform(a,b,key[-1],self.box(key))
    def child_keys(self,parent,u,w,typ):
        a,b=self.prototype(parent);box=self.box(parent)
        rr,ss,_=child_box(box,u,w)
        xa=side_pairs(scan(a),0,u,'base');xb=side_pairs(scan(b),0,w,'base')
        fa=normalized_difference_range(scan(a),xa[1],xa[0],box[0])
        fb=normalized_difference_range(scan(b),xb[1],xb[0],box[1])
        assert fa[0]>0 and fb[0]>0
        mapped=(box[2][0]*fb[0]/fa[1],box[2][1]*fb[1]/fa[0])
        if mapped[0]<Q(1,self.limit) or mapped[1]>self.limit:return None
        lower,upper=self.index(mapped[0]),self.index(mapped[1])
        if mapped[1]==self.power(upper):upper-=1
        keys=[self.key(a+u,b+w,typ,i) for i in range(lower,upper+1)]
        for key in keys:assert contains(self.box(key)[:2],(rr,ss))
        return keys


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--left',default='32113');p.add_argument('--right',default='4322')
    p.add_argument('--type',default='F');p.add_argument('--memory',type=int,default=2)
    p.add_argument('--base',default='21/20');p.add_argument('--length',type=int,default=12)
    p.add_argument('--nodes',type=int,default=1500);p.add_argument('--lookahead',type=int,default=3)
    p.add_argument('--steps',type=int,default=10000);p.add_argument('--output',default='width_catalog.json')
    p.add_argument('--types',default='T2,F');p.add_argument('--mixed-t2',action='store_true')
    p.add_argument('--seconds',type=float,default=None)
    args=p.parse_args();catalog=WidthCatalog(args.memory,Q(args.base),args.length,args.nodes,args.lookahead,
        pure_t2=not args.mixed_t2,types=tuple(args.types.split(',')))
    result=catalog.run(tuple(map(int,args.left)),tuple(map(int,args.right)),args.type,args.steps,args.seconds)
    result['settings']['coordinate']='persistent_width_ratio'
    (DATA/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'proof_complete':result['proof_complete'],'root_state':result['root_state'],
                      'rows':len(result['rows']),'reachable':len(result['reachable'])}),flush=True)
