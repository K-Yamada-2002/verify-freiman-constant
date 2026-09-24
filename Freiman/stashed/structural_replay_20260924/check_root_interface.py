#!/usr/bin/env python3
"""Exact obstruction to replacing the exploratory root by J(U,V) alone.

This does NOT refute filling the exploratory root, and is NOT a Cantor gap.
It only prevents an unjustified identification of the two requested intervals.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import sys,json
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'schecker_generalized'))
import explore as e
sys.path.insert(0,str(HERE.parent/'Freiman_Hall_ray_verification/verification/checks/global'))
import literal_covers as l

def enclosure(a,b,d,scale=10**30):
    k=isqrt(d*scale*scale)
    lo,hi=F(k,scale),F(k+1,scale)
    return (a+b*lo,a+b*hi) if b>=0 else (a+b*hi,a+b*lo)
def need(ok,msg):
    if not ok:raise ArithmeticError(msg)
pair=('32113','4322')
full=tuple(z+4 for z in e.hull(*pair));ordinary=l.interval(pair)
fbox=[enclosure(z.a,z.b,462) for z in full]
jbox=[enclosure(z.a,z.b,z.d) for z in ordinary]
need(fbox[0][1]<jbox[0][0] and jbox[1][1]<fbox[1][0],'strict endpoint separation')
witness=(jbox[1][1]+fbox[1][0])/2
need(fbox[0][1]<witness<fbox[1][0] and witness>jbox[1][1],'rational noncontainment witness')
result=dict(status='PASS_NONCONTAINMENT_CHECK',pair=pair,
    conclusion='The exploratory full root strictly contains the ordinary J root; direct substitution would lose requested targets.',
    not_claimed='No gap in the actual sum Cantor set is asserted.',
    full_endpoint_enclosures=[[str(q) for q in z] for z in fbox],
    ordinary_endpoint_enclosures=[[str(q) for q in z] for z in jbox],
    rational_target_in_full_hull_but_not_J=str(witness))
(HERE/'root_interface.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if 'enclosures' not in k},indent=2))
