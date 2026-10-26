"""Independent sign/corner replay for typed local certificates.

The square-root bracketing comparison below does not call E.sign. Uniform
denominator-coordinate inequalities are recomputed at all eight corners,
using direct Mobius evaluation. No search-screening decision is trusted.
Width-coordinate formula checks are regression checks, not closure proofs.
"""
import json
import random
from fractions import Fraction as Q
from functools import cmp_to_key
from itertools import product
from math import isqrt
from pathlib import Path
from layout import DATA
from typed_intervals import E,cf,endpoints,hull
from typed_boxes import Uniform,side_pairs
from typed_local_rows import rows
from width_catalog import normalized_difference_range,width,phi
from obstruction_probe import STATES,step,scan
from exact_cf import parameters
from box_certificates import child_box

BASE=DATA


def sign(value):
    v=E.cast(value)
    if all(c==0 for c in v.coeff):return 0
    scale=10**10
    while True:
        lo=hi=v.coeff[0]
        for c,d in zip(v.coeff[1:],(3,154,462)):
            q=isqrt(d*scale*scale)
            ends=[c*Q(q,scale),c*Q(q+1,scale)]
            lo+=min(ends);hi+=max(ends)
        if lo>0:return 1
        if hi<0:return -1
        scale*=scale


class CornerUniform(Uniform):
    def ge(self,x,y):
        def value(pair,r,s,rho):
            return ((-1)**len(self.a)*pair[0]/(1+r*pair[0])
                    +rho*(-1)**len(self.b)*pair[1]/(1+s*pair[1]))
        return all(sign(value(x,r,s,rho)-value(y,r,s,rho))>=0
                   for r,s,rho in product(*self.box))


def exact_union(intervals):
    intervals=sorted(intervals,key=cmp_to_key(lambda a,b:sign(a[0]-b[0])))
    result=[]
    for lo,hi in intervals:
        assert sign(hi-lo)>=0
        if result and sign(result[-1][1]-lo)>=0:
            if sign(hi-result[-1][1])>0:result[-1]=(result[-1][0],hi)
        else:result.append((lo,hi))
    return result


def main():
    checks={}
    records=json.loads((BASE/'typed_initial_cases.json').read_text())['records']
    for row in records:
        a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        pl,pu=hull(a,b,row['type'])
        ivs=[hull(a+tuple(u),b+tuple(w),t) for u,w,t in row['menu']]
        assert any(sign(pl-lo)>=0 and sign(hi-pu)>=0 for lo,hi in exact_union(ivs))
    checks['exact_point_covers']=len(records)
    for row in rows():
        a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        box=tuple(tuple(map(Q,pair)) for pair in row['box'])
        assert CornerUniform(a,b,row['type'],box).verify(row['menu'])
        assert all(len(u)+len(w)>0 for u,w,t in row['menu'])
    checks['independent_uniform_rows']=len(rows())
    # The two binary endpoint radicals are checked against 160-digit periodic
    # tails using a separate rational continued-fraction implementation.
    n=0
    for state in STATES:
        for digits,wanted in [((2,1),endpoints(state,'binary')[0]),
                              ((1,2),endpoints(state,'binary')[1])]:
            seq=digits*80
            def finite(t):
                for d in reversed(seq):t=1/(d+t)
                return t
            lo,hi=sorted((finite(Q(0)),finite(Q(1))))
            assert sign(wanted-lo)>=0 and sign(hi-wanted)>=0;n+=1
    checks['binary_endpoint_rational_enclosures']=n
    # Formula/enclosure regression, including states 313 and 3131, mixed-field
    # endpoints, both interval orientations and nonmonotone derivative cases.
    rng=random.Random(462);n=0
    for st in STATES:
        pool=list(endpoints(st,'base'))+list(endpoints(st,'binary'))
        for d in (1,2,3):
            if step(st,d) is not None:
                for lang in ('base','binary'):pool.extend(side_pairs(st,0,(d,),lang))
        for _ in range(50):
            x,y=rng.choice(pool),rng.choice(pool)
            lo=Q(rng.randrange(0,18),20);hi=lo+Q(1,10)
            ll,hh=normalized_difference_range(st,x,y,(lo,hi))
            for j in range(9):
                r=lo+(hi-lo)*Q(j,8)
                direct=(phi(r,x)-phi(r,y))/width(st,r)
                assert sign(direct-ll)>=0 and sign(hh-direct)>=0;n+=1
    checks['width_formula_enclosure_samples']=n
    # The width-ratio transition is checked against direct continued fractions
    # at genuine prefixes; numerator and denominator parities both occur.
    n=0
    for astr,bstr in [('32113','4322'),('321133','432212'),('3211311','43221')]:
        a,b=tuple(map(int,astr)),tuple(map(int,bstr));r,s,rho=parameters(a,b)
        R=rho*width(scan(b),s)/width(scan(a),r)
        for u,w in product([(),(1,),(2,),(3,),(1,2)],repeat=2):
            if scan(a+u) is None or scan(b+w) is None:continue
            xa=side_pairs(scan(a),0,u,'base');xb=side_pairs(scan(b),0,w,'base')
            fa=normalized_difference_range(scan(a),xa[1],xa[0],(r,r))[0]
            fb=normalized_difference_range(scan(b),xb[1],xb[0],(s,s))[0]
            rr,ss,rc=parameters(a+u,b+w)
            assert sign(R*fb/fa-rc*width(scan(b+w),ss)/width(scan(a+u),rr))==0;n+=1
    checks['exact_width_transitions']=n
    # Auxiliary hulls stay inside the full persistent-language cylinder hull.
    for typ in ('T2','L2','R2','B2'):
        a,b=(3,1,3,1),(3,1,3,1)
        lo,hi=hull(a,b,typ);fl,fh=hull(a,b,'F')
        assert sign(lo-fl)>=0 and sign(fh-hi)>=0
    result={'passed':True,'checks':checks,'closed_lemma_proved':False,'freiman_ray_proved':False}
    (BASE/'typed_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
