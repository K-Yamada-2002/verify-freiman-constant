"""Exact boxes using the derivative at the lower endpoint as scale.

Band types retain a prescribed subinterval of the full persistent hull. Their
cutoffs are rational; all endpoints and comparisons remain exact. A band is
only proved representable after successor closure, never from its definition.
"""
from fractions import Fraction as Q
from functools import lru_cache
from typed_intervals import E,channels
from typed_boxes import Uniform,side_pairs
from obstruction_probe import scan
from exact_cf import matrix


def band(kind):
    if not kind.startswith('band_'):return None
    _,a,b=kind.split('_');return Q(a),Q(b)


@lru_cache(None)
def expressions(a,b,u,w,kind):
    def side(word,ext,lang):
        return side_pairs(scan(word),len(word)%2,ext,lang)
    cut=band(kind)
    if cut is not None:
        alpha,beta=cut;aa=side(a,u,'base');bb=side(b,w,'base')
        mix=lambda ends,t:((1-t,ends[0]),(t,ends[1]))
        return (((mix(aa,alpha),mix(bb,alpha)),(mix(aa,1-beta),mix(bb,1-beta))),)
    result=[]
    for la,lb in channels(kind):
        aa=side(a,u,la);bb=side(b,w,lb)
        result.append(((((Q(1),aa[0]),),((Q(1),bb[0]),)),
                       (((Q(1),aa[1]),),((Q(1),bb[1]),))))
    return tuple(result)


@lru_cache(maxsize=100000)
def delta_range(anchor,x,y,bounds):
    factor=x-y
    if factor==0:return E.cast(0),E.cast(0)
    A=2*anchor-x-y;B=anchor*(x+y)-2*x*y
    vals=[A+B*r for r in bounds]
    def value(r):return factor*((1+r*anchor)/(1+r*x))*((1+r*anchor)/(1+r*y))
    if min(vals)>=0 or max(vals)<=0:
        vs=[value(r) for r in bounds]
    else:
        aa=[(1+r*anchor)/(1+r*x) for r in bounds]
        bb=[(1+r*anchor)/(1+r*y) for r in bounds]
        vs=[factor*a*b for a in aa for b in bb]
    return min(vs),max(vs)


@lru_cache(maxsize=100000)
def expression_range(anchor,x,y,bounds,parity):
    coeff={}
    for c,z in x:coeff[z]=coeff.get(z,Q(0))+c
    for c,z in y:coeff[z]=coeff.get(z,Q(0))-c
    assert sum(coeff.values())==0
    positive=[[c,z] for z,c in coeff.items() if c>0]
    negative=[[-c,z] for z,c in coeff.items() if c<0]
    lo=hi=E.cast(0);i=j=0
    while i<len(positive) and j<len(negative):
        mass=min(positive[i][0],negative[j][0])
        ll,hh=delta_range(anchor,positive[i][1],negative[j][1],bounds)
        if parity:ll,hh=-hh,-ll
        lo+=mass*ll;hi+=mass*hh
        positive[i][0]-=mass;negative[j][0]-=mass
        if not positive[i][0]:i+=1
        if not negative[j][0]:j+=1
    assert i==len(positive) and j==len(negative)
    return lo,hi


def anchor(word):return side_pairs(scan(word),len(word)%2,(),'base')[0]


@lru_cache(maxsize=30000)
def derivative_fraction(word,ext,bounds):
    x=anchor(word);y=anchor(word+ext);a,b,c,d=matrix(ext)
    vals=[]
    for r in bounds:
        z=(1+r*x)/((c+r*a)*y+d+r*b);vals.append(z*z)
    return min(vals),max(vals)


class AnchorUniform(Uniform):
    def __init__(self,a,b,kind,box):
        self.a=a;self.b=b;self.kind=kind;self.box=box
        self.parent=expressions(a,b,(),(),kind);self.cache={};self.checks=0
    def get(self,v):return expressions(self.a,self.b,*v)
    def ge(self,x,y):
        key=x,y
        if key not in self.cache:
            self.checks+=1
            # Discovery-only rejection. Every accepted comparison still uses
            # exact interval bounds below, including equality at an endpoint.
            for r in self.box[0]:
                for s in self.box[1]:
                    aa=float_side(self.a,x[0],r)-float_side(self.a,y[0],r)
                    bb=float_side(self.b,x[1],s)-float_side(self.b,y[1],s)
                    if min(aa+float(S)*bb for S in self.box[2]) < -1e-10:
                        self.cache[key]=False;return False
            aa=expression_range(anchor(self.a),x[0],y[0],self.box[0],len(self.a)%2)
            bb=expression_range(anchor(self.b),x[1],y[1],self.box[1],len(self.b)%2)
            self.cache[key]=(aa[0]+min(S*v for S in self.box[2] for v in bb))>=0
        return self.cache[key]
    def numeric(self,vertex):
        r,s,S=map(lambda z:float((z[0]+z[1])/2),self.box)
        def side(word,exp,r):
            x0=float(anchor(word))
            return sum(float(c)*(-1)**len(word)*(float(x)-x0)*(1+r*x0)/(1+r*float(x)) for c,x in exp)
        values=[(side(self.a,lo[0],r)+S*side(self.b,lo[1],s),
                 side(self.a,hi[0],r)+S*side(self.b,hi[1],s)) for lo,hi in self.get(vertex)]
        return min(p[0] for p in values),max(p[1] for p in values)


@lru_cache(maxsize=100000)
def float_side(word,exp,r):
    r=float(r);x0=float(anchor(word))
    return sum(float(c)*(-1)**len(word)*(float(x)-x0)*(1+r*x0)/(1+r*float(x)) for c,x in exp)
