"""Exact Q(sqrt(2),sqrt(5)) arithmetic, adapted from Freiman E."""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import total_ordering,lru_cache
from math import isqrt,gcd


@total_ordering
@dataclass(frozen=True)
class E:
    coeff: tuple=(Q(0),Q(0),Q(0),Q(0))
    basis=(1,2,5,10)

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
