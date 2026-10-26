"""Rational interface proof for replacing a core past in a palindromic SFT."""
from fractions import Fraction as Q
from itertools import product
from spectral_rational import RationalBounds


def prove(a,b,center,forbidden,damage=False):
    bad=tuple(tuple(w) for w in forbidden)
    assert all(w==w[::-1] and 2 not in w for w in bad)
    memory=max(map(len,bad))-1
    bounds=RationalBounds(bad,backward=memory,precision=60)
    assert bounds.legal(a) and bounds.legal(b)
    interfaces=[]
    for side,near,other in [('left',a,b),('right',b,a)]:
        prefix=near[::-1]+(center,)+other
        terminal=bounds.tail(other[-memory:],True)[0],bounds.tail(other[-memory:],False)[1]
        past=tuple(sorted(bounds.cf(prefix,t) for t in terminal))
        if damage:past=Q(2),Q(3)
        checks=[]
        for first in product((1,2,3),repeat=memory):
            if not bounds.legal(near+first):continue
            low=bounds.tail(first[::-1],True)[1]
            high=bounds.tail(first[::-1],False)[0]
            assert low<=past[0]<=past[1]<=high
            checks.append(dict(first=''.join(map(str,first)),minimum_upper=str(low),maximum_lower=str(high)))
        assert checks
        interfaces.append(dict(side=side,past=[str(x) for x in past],checks=checks))
    core=a[::-1]+(center,)+b
    values=[]
    for i,d in enumerate(core):
        if i==len(a):continue
        value=d+bounds.upper(core[:i][::-1],a)+bounds.upper(core[i+1:],b)
        values.append(dict(position=i-len(a),upper=str(value)))
    return dict(a=''.join(map(str,a)),b=''.join(map(str,b)),center=center,
                passed=True,interfaces=interfaces,core_values=values,
                core_upper=str(max(Q(v['upper']) for v in values)),
                scope='Appended positions compare to legal bilateral sequences; the finite core has the separately listed rational bound.')
