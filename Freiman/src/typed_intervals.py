"""Persistent 31313 avoidance plus resettable Schecker auxiliary tail types.

F: both tails obey the persistent language. T2: one fresh tail uses digits
1,2 and the other obeys the persistent language, with the two assignments
united before taking the hull. The C(2) condition is NOT imposed on the fixed
prefix and is NOT a constraint on the final limiting pair.

Exact endpoints lie in the linear span of 1,sqrt(3),sqrt(154),sqrt(462).
Only single-quadratic expressions are inverted in continued fractions.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import total_ordering,lru_cache
from math import isqrt,gcd
from exact_cf import matrix,tail_endpoint
from obstruction_probe import scan


@total_ordering
@dataclass(frozen=True)
class E:
    coeff: tuple=(Q(0),Q(0),Q(0),Q(0))
    basis=(1,3,154,462)

    def __post_init__(self):object.__setattr__(self,'coeff',tuple(map(Q,self.coeff)))
    @staticmethod
    def cast(x):return x if isinstance(x,E) else E((Q(x),0,0,0))
    @staticmethod
    def quad(a,b,d):
        out=[Q(a),Q(0),Q(0),Q(0)];out[E.basis.index(d)]=Q(b);return E(tuple(out))
    def __add__(self,x):return E(tuple(a+b for a,b in zip(self.coeff,self.cast(x).coeff)))
    __radd__=__add__
    def __neg__(self):return E(tuple(-x for x in self.coeff))
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        other=self.cast(x);out=[Q(0)]*4
        for i,a in enumerate(self.coeff):
            if not a:continue
            for j,b in enumerate(other.coeff):
                if not b:continue
                g=gcd(self.basis[i],self.basis[j]);rad=self.basis[i]*self.basis[j]//(g*g)
                out[self.basis.index(rad)]+=a*b*g
        return E(tuple(out))
    __rmul__=__mul__
    def __truediv__(self,x):
        other=self.cast(x);irr=[i for i in range(1,4) if other.coeff[i]]
        if not irr:return E(tuple(c/other.coeff[0] for c in self.coeff))
        if len(irr)>1:raise ValueError('Only single-quadratic inverses are required')
        i=irr[0];a=other.coeff[0];b=other.coeff[i]
        norm=a*a-self.basis[i]*b*b
        inv=[Q(0)]*4;inv[0]=a/norm;inv[i]=-b/norm
        return self*E(tuple(inv))
    def __rtruediv__(self,x):return self.cast(x)/self
    def sign(self):
        if not any(self.coeff):return 0
        nonzero=[i for i in range(1,4) if self.coeff[i]]
        if not nonzero:return (self.coeff[0]>0)-(self.coeff[0]<0)
        if len(nonzero)==1:
            i=nonzero[0];a,b=self.coeff[0],self.coeff[i]
            if not a or (a>0)==(b>0):return 1 if b>0 else -1
            t=a*a-self.basis[i]*b*b
            return ((t>0)-(t<0))*(1 if a>0 else -1)
        scale=10**12
        while True:
            lo=hi=self.coeff[0]
            for i in nonzero:
                z=isqrt(self.basis[i]*scale*scale)
                v=[self.coeff[i]*Q(z,scale),self.coeff[i]*Q(z+1,scale)]
                lo+=min(v);hi+=max(v)
            if lo>0:return 1
            if hi<0:return -1
            scale*=scale
    def __eq__(self,x):
        try:return self.coeff==self.cast(x).coeff
        except (TypeError,ValueError):return False
    def __lt__(self,x):return (self-x).sign()<0
    @lru_cache(maxsize=50000)
    def __float__(self):
        # Some derivative ratios have huge conjugates: summing floating
        # coefficients could return a negative number for a positive value.
        # Refine rational radical enclosures until both round to one float.
        if not any(self.coeff[1:]):return float(self.coeff[0])
        scale=10**32
        while True:
            lo=hi=self.coeff[0]
            for c,d in zip(self.coeff[1:],self.basis[1:]):
                if not c:continue
                q=isqrt(d*scale*scale)
                vals=(c*Q(q,scale),c*Q(q+1,scale))
                lo+=min(vals);hi+=max(vals)
            ll,hh=float(lo),float(hi)
            if ll==hh:return ll
            scale*=scale
    def data(self):return [str(x) for x in self.coeff]


BINARY=(E.quad(Q(-1,2),Q(1,2),3),E.quad(-1,1,3))


def cf(word,t):
    a,b,c,d=matrix(tuple(word));return (a*t+b)/(c*t+d)


@lru_cache(None)
def endpoints(state,kind):
    if kind=='binary':return BINARY
    return tuple(E.quad(v.a,v.b,462) for v in (tail_endpoint(state,True),tail_endpoint(state,False)))


def channels(kind):
    if kind=='F':return (('base','base'),)
    if kind=='T2':return (('binary','base'),('base','binary'))
    if kind=='L2':return (('binary','base'),)
    if kind=='R2':return (('base','binary'),)
    if kind=='B2':return (('binary','binary'),)
    raise ValueError(kind)


@lru_cache(None)
def hull(a,b,kind='F'):
    sa,sb=scan(a),scan(b)
    if sa is None or sb is None:raise ValueError('Persistent forbidden word')
    values=[]
    for ka,kb in channels(kind):
        aa=sorted(cf(a,t) for t in endpoints(sa,ka));bb=sorted(cf(b,t) for t in endpoints(sb,kb))
        values.append((aa[0]+bb[0],aa[1]+bb[1]))
    return min(v[0] for v in values),max(v[1] for v in values)


def merged(intervals):
    out=[]
    for lo,hi in sorted(intervals):
        if out and lo<=out[-1][1]:out[-1]=(out[-1][0],max(out[-1][1],hi))
        else:out.append((lo,hi))
    return out


def normalized_interval(r,s,rho,pa,pb,ea,eb,kind):
    def one(r,p,ext,lang):
        _,st,(a,b,c,d)=ext
        ts=endpoints(st,lang)
        vals=[]
        for t in ts:
            x=(a*float(t)+b)/(c*float(t)+d)
            vals.append((-1)**p*x/(1+r*x))
        return min(vals),max(vals)
    vals=[]
    for ka,kb in channels(kind):
        aa=one(r,pa,ea,ka);bb=one(s,pb,eb,kb)
        vals.append((aa[0]+rho*bb[0],aa[1]+rho*bb[1]))
    return min(v[0] for v in vals),max(v[1] for v in vals)
