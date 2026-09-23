#!/usr/bin/env python3
"""Exact invariant for the six extremal periodic phases and their returns.

This closes the parameter update along an extremal return, not an interval
cover. The regions between the returning endpoint cylinders remain unproved.
"""
import argparse
import json
from pathlib import Path

from explore import Q, STATES, extreme_tail, matrix, state_of, transform


def anchored_difference_range(anchor,x,y,rlo,rhi):
    """Exact range of (x-y)(1+anchor*r)^2/((1+x*r)(1+y*r)).

    For a legal tail anchor at either extreme, anchor lies on the same side
    of both x and y. The logarithmic derivative of the positive factor is
    2*anchor/(1+anchor*r)-x/(1+x*r)-y/(1+y*r), whose sign is constant because
    z/(1+z*r) increases with z. Thus only the two r endpoints are needed.
    """
    assert 0<=rlo<=rhi and min(anchor,x,y)>0
    assert anchor<=min(x,y) or anchor>=max(x,y)
    values=[(x-y)*(1+anchor*r)*(1+anchor*r)/((1+x*r)*(1+y*r))
            for r in (rlo,rhi)]
    return min(values),max(values)


def verify():
    eigenvalue = Q(43, 2)
    rows = []
    for state in STATES:
        for high in (False, True):
            z, preperiod, period = extreme_tail(state, high)
            if preperiod:
                continue
            a, b, c, d = matrix(period)
            assert len(period) == 6
            assert state_of(state+period) == state
            assert a*d-b*c == 1
            assert a*z+b == eigenvalue*z
            assert c*z+d == eigenvalue
            rows.append({'state': state, 'high': high, 'period': period})
    assert len(rows) == 6
    # Both returns defining A_(n+1) have the same eigenvalue, so these
    # identities imply invariance for every n, with no sampled-n argument.
    alpha = extreme_tail('3', True)[0]
    beta = extreme_tail('', False)[0]
    for period, z in (('131213', alpha), ('313121', beta)):
        a, b, c, d = matrix(period)
        assert a*z+b == eigenvalue*z and c*z+d == eigenvalue
        assert transform(period, z) == z
    _, _, c, d = matrix('32113')
    _, _, cc, dd = matrix('4322')
    ratio = (c*alpha+d)/(cc*beta+dd)
    ratio = ratio*ratio
    return {'status': 'exact periodic parameter invariant; not a filling certificate',
            'eigenvalue': eigenvalue.record(),
            'periodic_phases': rows,
            'initial_family_anchor_ratio': ratio.record()}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    result = verify()
    print(json.dumps(result, indent=2))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
