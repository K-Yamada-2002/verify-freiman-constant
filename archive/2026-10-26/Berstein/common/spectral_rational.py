"""All-position bounds using finite backward windows and rational CF bounds.

Unlike the Fibonacci error bound, the far-position calculation keeps the
actual backward digits. A terminal [0,1] encloses every remaining past.
This module imports neither of the algebraic spectral implementations.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product


class RationalBounds:
    def __init__(self, forbidden, backward=8, precision=40):
        self.forbidden = tuple(tuple(w) for w in forbidden)
        assert self.forbidden and all(w[::-1] in self.forbidden for w in self.forbidden)
        self.memory = max(map(len,self.forbidden))-1
        self.backward = backward
        self.precision = precision
        self.tail = lru_cache(None)(self._tail)
        self.matrix = lru_cache(None)(self._matrix)

    def legal(self,w):
        return not any(w[i:i+len(b)] == b for b in self.forbidden
                       for i in range(len(w)-len(b)+1))

    @staticmethod
    def _matrix(w):
        a,b,c,d = 1,0,0,1
        for v in w:
            a,b,c,d = b,a+v*b,d,c+v*d
        return a,b,c,d

    def cf(self,w,x):
        a,b,c,d = self.matrix(w)
        # One rational reduction instead of four arithmetic operations and
        # their repeated gcds. This is the same exact Mobius expression.
        x = Q(x)
        return Q(a*x.numerator+b*x.denominator,c*x.numerator+d*x.denominator)

    def _tail(self,history,minimum):
        out = ()
        for n in range(self.precision):
            choices = [d for d in (1,2,3) if self.legal(history+out+(d,))]
            # The supported forbidden words contain no 2: appending only 2
            # is always possible. Thus no greedy choice is a dead end.
            assert all(2 not in w for w in self.forbidden)
            d = max(choices) if minimum == (n%2 == 0) else min(choices)
            out += (d,)
        return tuple(sorted(self.cf(out,t) for t in (Q(0),Q(1))))

    def upper(self,prefix,history):
        bounds = self.tail(history[-self.memory:],len(prefix)%2 == 1)
        return self.cf(prefix,bounds[1 if len(prefix)%2 == 0 else 0])

    @lru_cache(None)
    def far(self):
        n = self.backward
        assert n >= self.memory
        values = []
        count = 0
        for past in product((1,2,3),repeat=n):
            w = past+(3,)
            if not self.legal(w):
                continue
            # Digits 1 and 2 have local value <4; digit 3 is the only case
            # needing enumeration. The past beyond this window is arbitrary.
            back = max(self.cf(past[::-1],t) for t in (Q(0),Q(1)))
            value = 3+back+self.upper((),w)
            values.append((value,past))
            count += 1
        bound,witness = max(values)
        return max(bound,Q(4)),witness,count

    def root(self,a,b,center=4):
        assert self.legal(a) and self.legal(b)
        core = a[::-1]+(center,)+b
        candidates = [(self.far()[0],{'type':'far','past':self.far()[1]}),
                      (Q(4),{'type':'digits_1_2'})]
        for i,d in enumerate(core):
            if i == len(a):
                continue
            value = d+self.upper(core[:i][::-1],a)+self.upper(core[i+1:],b)
            candidates.append((value,{'type':'core','position':i-len(a)}))
        counted = 0
        for side,near,other in [('left',a,b),('right',b,a)]:
            frontier = [()]
            # At distance >n the last n backward digits and the current
            # digit are all in the legal appended word, so far() applies.
            for distance in range(1,self.backward+1):
                children = []
                for ext in frontier:
                    for d in (1,2,3):
                        w = ext+(d,)
                        if not self.legal(near+w):
                            continue
                        children.append(w)
                        counted += 1
                        if d != 3:
                            continue
                        back = (near+ext)[::-1]+(center,)+other
                        if self.far()[0]>=Q(9,2) and back[0]>=2:
                            continue  # value <3+1/2+1=4.5
                        value = d+self.upper(back,other)+self.upper((),near+w)
                        candidates.append((value,{'type':'near','side':side,
                                                 'distance':distance,'extension':w}))
                frontier = children
        theta,witness = max(candidates,key=lambda v:v[0])
        return dict(theta=str(theta),theta_decimal=float(theta),witness=witness,
                    forbidden=self.forbidden,backward=self.backward,
                    tail_precision=self.precision,far_upper=str(self.far()[0]),
                    far_witness=self.far()[1],far_windows=self.far()[2],
                    near_prefixes=counted,
                    scope='Uniform over all infinite legal tails and all noncentral positions.')
