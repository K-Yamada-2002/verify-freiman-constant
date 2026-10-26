"""Remove the tail-error term by replacing the finite core's past.

For each legal first four digits of an appended tail, the core's backward CF
lies between the extrema of legal pasts compatible with that context. Depending
on parity, one of these legal pasts dominates every later backward CF. Keeping
the future unchanged gives a legal bilateral 31313-free comparison sequence.
Thus every appended position has value at most the exact bulk maximum.

Both quadratic arithmetic and independent rational CF enclosures check the
finite interface inequalities. No interval filling is inferred here.
"""
import sys
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'Freiman/src'))
from exact_cf import K,cf,tail_endpoint,periodic
from obstruction_probe import scan
from spectral_bounds import bulk_maximum,maximize
from spectral_rational import RationalBounds

BAD=(3,1,3,1,3)
BULK=K(0,Q(4,19))


def prove_root(a,b,damage_past=False):
    assert scan(a) is not None and scan(b) is not None
    rational=RationalBounds([BAD],backward=4,precision=60)
    interfaces=[]
    for side,near,other in [('left',a,b),('right',b,a)]:
        prefix=near[::-1]+(4,)+other
        exact=sorted(cf(prefix,tail_endpoint(scan(other),t)) for t in (True,False))
        # Independent terminal enclosures for all allowed other-side tails.
        tlo=rational.tail(other[-4:],True)[0]
        thi=rational.tail(other[-4:],False)[1]
        past=tuple(sorted(rational.cf(prefix,t) for t in (tlo,thi)))
        assert K(past[0])<=exact[0]<=exact[1]<=K(past[1])
        if damage_past:
            past=Q(2),Q(3)
        states=set();contexts=0
        checks=[]
        for first in product((1,2,3),repeat=4):
            assert rational.legal(near+first)==(scan(near+first) is not None)
            if not rational.legal(near+first):continue
            history=first[::-1]
            state=scan(history)
            low,high=tail_endpoint(state,True),tail_endpoint(state,False)
            assert low<=exact[0]<=exact[1]<=high
            # Safe directions: even the upper enclosure of the legal minimum
            # is below the lower enclosure of every possible core past, etc.
            legal_low_upper=rational.tail(history,True)[1]
            legal_high_lower=rational.tail(history,False)[0]
            assert legal_low_upper<=past[0]<=past[1]<=legal_high_lower
            contexts+=1;states.add(state)
            checks.append(dict(first=''.join(map(str,first)),state=list(state),
                               legal_minimum_upper=str(legal_low_upper),
                               legal_maximum_lower=str(legal_high_lower)))
        assert contexts>0
        interfaces.append(dict(side=side,past_exact=[x.data() for x in exact],
                               past_rational=[str(x) for x in past],
                               compatible_states=[list(s) for s in sorted(states)],
                               legal_four_digit_contexts=contexts,checks=checks))
    core=a[::-1]+(4,)+b
    core_values=[]
    rational_core=[]
    for i,d in enumerate(core):
        if i==len(a):continue
        left,right=core[:i][::-1],core[i+1:]
        value=d+maximize(left,scan(a))+maximize(right,scan(b))
        upper=d+rational.upper(left,a)+rational.upper(right,b)
        assert value<=K(upper)
        core_values.append(dict(position=i-len(a),exact=value.data(),upper=str(upper)))
        rational_core.append(upper)
    # A rational-only comparison with a strict lower bound for BULK.
    lower=Q('4.5250916')
    assert (19*lower)**2<16*462
    theta=max(BULK,K(max(rational_core)))
    assert bulk_maximum()[0]==BULK
    return dict(a=''.join(map(str,a)),b=''.join(map(str,b)),passed=True,
                theta_upper=theta.data(),interfaces=interfaces,core_values=core_values,
                core_strictly_below_bulk=max(rational_core)<lower,
                rational_only_interface_checks=True,
                interpretation='All appended positions compare to a legal bilateral base sequence; the finite core is bounded separately.')


def periodic_bulk_endpoint():
    word=(3,1,3,1,2,1)
    assert scan(word*3) is not None
    values=[]
    for i,d in enumerate(word):
        left=tuple(word[(i-j)%len(word)] for j in range(1,len(word)+1))
        right=tuple(word[(i+j)%len(word)] for j in range(1,len(word)+1))
        x,y=periodic(left),periodic(right)
        assert cf(left,x)==x and cf(right,y)==y and 0<x<1 and 0<y<1
        values.append(d+x+y)
    assert max(values)==BULK
    return dict(word='313121',local_values=[v.data() for v in values],
                maximum=BULK.data(),in_L_and_M=True,
                reason='A periodic sequence has limsup equal to its maximum.')
