#!/usr/bin/env python3
"""Exact identities for both endpoints of every exploratory initial A_n."""
from pathlib import Path
from fractions import Fraction as F
import sys,json
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'schecker_generalized'))
import explore as e

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)
S='313121';P='131213';R='131312'
xi=e.periodic(S);zeta=e.periodic(P);eta=e.periodic(R);lam=e.Q(43,2)
for w,z in ((S,xi),(P,zeta),(R,eta)):
    a,b,c,d=e.matrix(w)
    need(a+d==86 and a*d-b*c==1,'common recurrence')
    need(a*z+b==lam*z and c*z+d==lam,'positive common eigenvalue')
    need(e.transform(w,z)==z,'period fixed point')
need(e.transform('3',zeta)==xi,'minimum endpoint word identity')
need(e.extreme_tail('3',True)[0]==zeta,'left lower extreme for odd prefix')
need(e.extreme_tail('3',False)[0]==e.transform('3',zeta),'left upper extreme for odd prefix')
need(e.extreme_tail('',False)[0]==xi and e.extreme_tail('',True)[0]==eta,'right extremes')
for prefix in ('3211','4322'):
    need(e.state_of(prefix+S)==e.state_of(prefix+S+S),'all-positive-n state')
need(e.state_of('3211'+S+'3')=='3' and e.state_of('32113')=='3','left state for all n')
need(e.state_of('4322'+S)=='' and e.state_of('4322')=='','right state for all n')
for prefix,period in (('321133',P),('4322',R),('3211'+S+'33',P),('4322'+S,R)):
    need(e.state_of(prefix)==e.state_of(prefix+period),'upper periodic language return')
cf=4+e.transform('3211',xi)+e.transform('4322',xi)
need(cf==e.Q(F(2221564096,491993569),F(283748,491993569)),'Freiman endpoint exact value')
for w in ('32113','4322'):
    _,_,c,d=e.matrix(w);need(F(1,4)<=F(c,d)<=F(4,5),'initial continuant ratio')
for digit in (1,2,3):
    need(F(1,4)<=1/(digit+F(4,5))<=1/(digit+F(1,4))<=F(4,5),'invariant ratio box')
# The invariant interval and strict determinant factor are algebraic induction,
# not sampled powers. f(1/(86-x))=(x^2-86*x+1)/(86-x)^2.
need(F(1,86)<=F(85,7309)<F(1,85),'recurrence box')
need((1-86*86+86*86,86-172,1)==(1,-86,1),'determinant factor identity')
result=dict(status='PASS_ALL_INDEX_ENDPOINT_IDENTITIES',periods=[S,P,R],
    eigenvalue=lam.record(),minimum=cf.record(),
    upper_formula='4 + T_(3211 S^n 33)([0;overline(131213)]) + T_(4322 S^n)([0;overline(131312)])',
    scope='Word-state returns, fixed-point identities and recurrence imply the formulas for every n and m.')
(HERE/'endpoint_returns.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'])
