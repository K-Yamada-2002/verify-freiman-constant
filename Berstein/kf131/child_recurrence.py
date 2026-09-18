#!/usr/bin/env python3
"""Child covers and a genuine return branch on an invariant shape domain.

The other branches remain obligations. This is NOT an interior proof.
"""
import json
from pathlib import Path
from exact import Q, F
from uniform_cover import ROOT, CHILDREN, difference

# Every endpoint label is relative to the original pair U,V (both odd).
A1 = (('122', False, '132', False), ('113', True, '112', True))
A2 = (('1113', True, '12', True), ('1132', False, '32', False))
B1 = (('221', False, '132', False), ('212', True, '113', True))
B2 = (('321', False, '132', True), CHILDREN[1][1])
# Both appended 2s reverse the endpoint order of the root type.
RETURN = (('2211', False, '232', True), ('2122', False, '213', True))
D = (('231', False, '331', False), ROOT[1])
OFFERS = (A1, A2, B1, B2, RETURN, D)
PREFIXES = (('1', '1'), ('11', ''), ('2', '1'), ('3', '1'), ('2', '2'), ('2', '3'))


def compute():
    box = ((Q(F(9, 25)), Q(F(9, 20))),
           (Q(F(9, 25)), Q(F(9, 20))),
           (Q(F(489, 1000)), Q(F(512, 1000))))
    checks = []
    comparisons = [
        ('A left', CHILDREN[0][0], A1[0]),
        ('A1-A2 contact', A1[1], A2[0]),
        ('A right', A2[1], CHILDREN[0][1]),
        ('B left', CHILDREN[1][0], B1[0]),
        ('B1-B2 contact', B1[1], B2[0]),
        ('B right', B2[1], CHILDREN[1][1]),
        ('root A-B contact', CHILDREN[0][1], CHILDREN[1][0]),
        ('B-return contact', CHILDREN[1][1], RETURN[0]),
        ('return-D contact', RETURN[1], D[0]),
        ('root left', ROOT[0], A1[0]),
        ('root right', D[1], ROOT[1]),
        ('return nested left', RETURN[0], ROOT[0]),
        ('return nested right', ROOT[1], RETURN[1]),
    ]
    comparisons += [(f'offer {i} width', hi, lo) for i, (lo, hi) in enumerate(OFFERS)]
    for name, e1, e2 in comparisons:
        lo, hi = difference(e1, e2, box)
        assert lo >= 0, (name, lo.record())
        if 'contact' in name or 'width' in name:
            assert lo > 0
        checks.append({'test': name, 'lower': lo.record(), 'upper': hi.record()})

    # The derivative ratio H(x)=q*(1+r*x)^2/(1+s*x)^2 is monotone.
    # Bounding H at x=0,1 bounds it on [0,1]. Under a common appended
    # word w, H_new(x)=H(phi_w(x)), by the chain rule.
    rlo,rhi=F(9,25),F(9,20)
    qlo,qhi=F(489,1000),F(512,1000)
    for u,v in [('112','122')]:
        from exact import matrix
        _,_,cu,du=matrix(u);_,_,cv,dv=matrix(v)
        r,s,q=F(cu,du),F(cv,dv),F(du*du,dv*dv)
        assert rlo<r<rhi and rlo<s<rhi
        assert qlo<q<qhi and qlo<q*((1+r)/(1+s))**2<qhi
    shape2=(1/(2+rhi),1/(2+rlo))
    shape12=((rlo+1)/(2*rlo+3),(rhi+1)/(2*rhi+3))
    for lo,hi in (shape2,shape12):
        assert rlo<lo<=hi<rhi
    return {'status': 'Uniform six-offer cover with ONE proved return branch; other branches UNPROVED',
            'shape_interval': [str(rlo), str(rhi)],
            'derivative_ratio_bounds': [str(qlo), str(qhi)],
            'domain_conditions': ['r,s in shape_interval',
                                  'q in derivative_ratio_bounds',
                                  'q*((1+r)/(1+s))^2 in derivative_ratio_bounds'],
            'return_shape_bounds': {'2':[str(z) for z in shape2],
                                    '12':[str(z) for z in shape12]},
            'root': ROOT, 'offers': OFFERS, 'prefixes': PREFIXES,
            'return_offer_index': 4, 'checks': checks}


if __name__ == '__main__':
    result = compute()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
