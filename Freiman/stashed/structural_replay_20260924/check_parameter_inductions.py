#!/usr/bin/env python3
"""All-index recurrence identities, with exact invariant intervals.

These discharge recurrence/envelope induction, not endpoint coverage on boxes.
No finite sampling of exponents is used.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)
def mm(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in (0,1)) for j in (0,1)) for i in (0,1))
def matrix(word):
    a=((1,0),(0,1))
    for digit in word:a=mm(a,((0,1),(1,int(digit))))
    return a
def add(a,b):
    return tuple(a[i]+b[i] for i in range(3))
def scale(c,a):return tuple(c*x for x in a)
def mul_linear(a,b):return (a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1])

S=matrix('313121');D=matrix('3');identity=((1,0),(0,1))
need(S==((14,19),(53,72)),'period matrix')
need(mm(S,S)==tuple(tuple(86*S[i][j]-identity[i][j] for j in (0,1)) for i in (0,1)),'Cayley-Hamilton S')
need(mm(D,D)==tuple(tuple(3*D[i][j]+identity[i][j] for j in (0,1)) for i in (0,1)),'Cayley-Hamilton digit3')
# x -> 1/(86-x) maps [0,1/85] strictly inside the upper bound.
xbox=(Q(0),Q(1,85)); ximage=(Q(1,86),1/(86-xbox[1]))
need(xbox[0]<=ximage[0]<=ximage[1]<xbox[1],'all-n envelope')
# f(x') = f(x)/(86-x)^2, f(x)=x^2-86*x+1; f(x_1)=1.
f=(1,-86,1); den=(86,-1)
transformed=add(add((1,0,0),scale(-86,(*den,0))),mul_linear(den,den))
need(transformed==f,'strict contact factor persists at all n')
# y -> 1/(3+y), decreasing, for any repetition k or p of digit3.
ybox=(Q(0),Q(1,3)); yimage=(1/(3+ybox[1]),Q(1,3))
need(ybox[0]<=yimage[0]<=yimage[1]<=ybox[1],'all-k/all-p envelope')
# For J_k parity subsequences, y_{k+2}=(3+y_k)/(10+3*y_k).
# Its derivative is 1/(10+3*y)^2, and positive fixed point solves y^2+3y-1=0.
need(10-3*3==1,'two-step positive derivative numerator')
result=dict(status='PASS',scope='All-index parameter induction only; box inequalities remain separate',
    period_matrix=S,digit3_matrix=D,
    x_base='0 at n=1; n=0 uses identity matrix separately',
    x_map='1/(86-x)',x_box=list(map(str,xbox)),x_image=list(map(str,ximage)),
    contact_factor_identity='f(1/(86-x)) = f(x)/(86-x)^2, f=x^2-86*x+1',
    y_base='0 at k=1 or p=1',y_map='1/(3+y)',y_box=list(map(str,ybox)),y_image=list(map(str,yimage)),
    parity_map='(3+y)/(10+3*y)')
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
