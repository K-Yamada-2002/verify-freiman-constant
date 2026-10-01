"""User's full-prefix I(U,V;B1,B2), with rigorous rational enclosures.

Unlike resettable tail constraints, forbidden words are checked in the entire
prefix and across its boundary. An empty language or channel stays empty.
Bounds are outer bounds, never a certificate that the sum fills its hull.
"""
from fractions import Fraction as Q
from functools import lru_cache
from exact_cf import cf


class Language:
    def __init__(self, forbidden, alphabet=(1,2,3,4)):
        self.alphabet=tuple(sorted(set(alphabet)))
        if not self.alphabet or any(d<=0 for d in self.alphabet):
            raise ValueError('Use a nonempty alphabet of positive integers')
        self.forbidden=tuple(sorted(set(map(tuple,forbidden))))
        if any(not w for w in self.forbidden):raise ValueError('Empty forbidden word')
        self.states=tuple(sorted({()}|{w[:i] for w in self.forbidden for i in range(1,len(w))}))
        self.edges={s:{d:self._step(s,d) for d in self.alphabet} for s in self.states}
        # Remove states without infinite continuations before choosing greedy digits.
        live=set(self.states)
        while True:
            new={s for s in live if any(t in live for t in self.edges[s].values())}
            if new==live:break
            live=new
        self.live=frozenset(live)

    def _step(self,s,d):
        w=s+(d,)
        if any(len(v)<=len(w) and w[-len(v):]==v for v in self.forbidden):return None
        return max((t for t in self.states if not t or w[-len(t):]==t),key=len)

    def scan(self,word):
        s=()
        for d in word:
            s=self.edges.get(s,{}).get(d)
            if s is None:return None
        return s if s in self.live else None

    @lru_cache(None)
    def extremal_tail(self,state,minimize):
        if state not in self.live:raise ValueError('No infinite continuation')
        seen={};digits=[];odd=True
        while (state,odd) not in seen:
            seen[state,odd]=len(digits)
            allowed=[d for d,t in self.edges[state].items() if t in self.live]
            d=max(allowed) if minimize==odd else min(allowed)
            digits.append(d);state=self.edges[state][d];odd=not odd
        cut=seen[state,odd]
        return tuple(digits[:cut]),tuple(digits[cut:])

    def endpoint(self,word,minimize,precision=100):
        word=tuple(word);state=self.scan(word)
        if state is None:return None
        pre,per=self.extremal_tail(state,minimize==(len(word)%2==0))
        digits=word+pre+(per*(precision//len(per)+1))[:precision]
        return tuple(sorted(cf(digits,t) for t in (Q(0),Q(1))))

    def hull(self,word,precision=100):
        lo=self.endpoint(tuple(word),True,precision)
        hi=self.endpoint(tuple(word),False,precision)
        return None if lo is None else (lo[0],hi[1])


def generalized_t(U,V,B1,B2,precision=100):
    """Return None or an outer enclosure of the hull of the two live channels."""
    intervals=[]
    for left,right in ((B1,B2),(B2,B1)):
        x,y=left.hull(U,precision),right.hull(V,precision)
        if x is not None and y is not None:intervals.append((x[0]+y[0],x[1]+y[1]))
    return None if not intervals else (min(x for x,y in intervals),max(y for x,y in intervals))


def successors(U,V,B1,B2,total_length=3):
    """Enumerate proper 3-successors with nonempty global-language channels."""
    from itertools import product
    for n in range(1,total_length+1):
        for h in range(n+1):
            for u in product((1,2,3),repeat=h):
                for v in product((1,2,3),repeat=n-h):
                    iv=generalized_t(tuple(U)+u,tuple(V)+v,B1,B2)
                    if iv is not None:yield u,v,iv
