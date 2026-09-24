#!/usr/bin/env python3
"""Uniform local 3-successor cover for every periodic initial A_n.

Proves a cover of numerical intervals, NOT recursive filling of its children.
The proof uses exact Q(sqrt(462)) signs and a rational parameter box.
"""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
from explore import Q, matrix, transform, extreme_tail, hull, merge


def mul(a,b):
    aa,ab,ac,ad=a;ba,bb,bc,bd=b
    return (aa*ba+ab*bc,aa*bb+ab*bd,ac*ba+ad*bc,ac*bb+ad*bd)


def params(u,v):
    _,_,cu,du=u;_,_,cv,dv=v
    return F(cu,du),F(cv,dv),F(du*du,dv*dv)


def compute():
    xi=extreme_tail('',False)[0]
    t=extreme_tail('',True)[0]
    zeta=extreme_tail('3',True)[0]
    a=transform('11',xi);b=transform('2',xi)
    # Endpoint identities used by the symbolic proof.
    assert transform('3',zeta)==xi
    assert transform('13',zeta)==t
    assert extreme_tail('31',True)[0]==transform('1',xi)
    assert extreme_tail('3',True)[0]==transform('1',extreme_tail('31',False)[0])
    assert a>b and t>xi and t>a
    assert transform('2',xi)>transform('2',t)

    r_bounds=(F(1,4),F(3,10))
    s_bounds=(F(2,5),F(3,4))
    q_bounds=(F(2,3),F(5,6))
    # A_high - B_low = -(a-b)/((1+r*a)(1+r*b))
    #                  +q*(t-xi)/((1+s*t)(1+s*xi)).
    lower=(-(a-b)/((1+r_bounds[0]*a)*(1+r_bounds[0]*b))
           +q_bounds[0]*(t-xi)/((1+s_bounds[1]*t)*(1+s_bounds[1]*xi)))
    assert lower>0

    rows=[]
    initial=params(matrix('32113'),matrix('4322'))
    rows.append({'case':'n=0','r':str(initial[0]),'s':str(initial[1]),'q':str(initial[2])})
    for x in (F(0),F(1,85)):
        mp=(14-x,F(19),F(53),72-x)
        u=mul(mul(matrix('3211'),mp),matrix('3'))
        v=mul(matrix('4322'),mp)
        assert all(y>0 for y in u+v)
        r,s,q=params(u,v)
        rows.append({'case':f'x={x}','r':str(r),'s':str(s),'q':str(q)})
    for row in rows:
        for key,bounds in [('r',r_bounds),('s',s_bounds),('q',q_bounds)]:
            assert bounds[0]<=F(row[key])<=bounds[1]
    # Each matrix entry is affine in x. Denominators and numerators above are
    # positive at both endpoints, hence throughout the interval. Ratios of
    # affine functions are monotone (or constant); their positive squares
    # are monotone too. Thus endpoint checks prove the whole parameter box.

    samples=[]
    for n in range(4):
        u,v='3211'+'313121'*n+'3','4322'+'313121'*n
        aa=hull(u+'1',v);bb=hull(u+'2',v)
        jj=(transform(u+'2',xi)+transform(v+'11',xi),hull(u,v+'1')[1])
        hh=hull(u,v)
        assert aa[0]==hh[0] and jj[1]==hh[1]
        assert merge([aa,bb,jj])==[hh]
        samples.append({'n':n,'left':u,'right':v,
                        'J_lower':jj[0].record(),'J_upper':jj[1].record()})
    return {'status':'PROVED uniform local numerical cover; child filling remains unproved',
            'statement':'I(U_n,V_n) = I(U_n1,V_n) union I(U_n2,V_n) union J(U_n,V_n1), n>=0',
            'J':'[T_(U2)(xi)+T_(V1)(xi), max I(U,V)] for odd/odd prefixes in states 3,empty',
            'xi':xi.record(),'zeta':zeta.record(),
            'parameter_box':{k:[str(a),str(b)] for k,(a,b) in
                             [('r',r_bounds),('s',s_bounds),('q',q_bounds)]},
            'parameter_endpoint_checks':rows,
            'successor_parameter_boxes':{
                'I(U1,V)':{'states':['31',''],'parities':[0,0],
                            'r':['10/13','4/5'],'s':['2/5','3/4'],'q':['25/24','169/120']},
                'I(U2,V)':{'states':['',''],'parities':[0,0],
                            'r':['10/23','4/9'],'s':['2/5','3/4'],'q':['27/8','529/120']},
                'J(U,V1)':{'states':['3',''],'parities':[1,1],
                            'r':['1/4','3/10'],'s':['4/7','5/7'],'q':['32/147','125/294']}},
            'first_contact_uniform_lower_bound':lower.record(),
            'second_contact':'positive + positive: G_r(phi_2(xi))-G_r(phi_2(T)) + q*(G_s(T)-G_s(phi_11(xi)))',
            'finite_samples_consistency_only':samples}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    result=compute();text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(json.dumps({k:result[k] for k in ('status','statement','first_contact_uniform_lower_bound')},indent=2))


if __name__=='__main__':main()
