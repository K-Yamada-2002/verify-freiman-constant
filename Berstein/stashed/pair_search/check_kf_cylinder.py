#!/usr/bin/env python3
"""Test replacing proposition 7 by a single cylinder of the 131-only set."""
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal,localcontext
from search import Model
from simple_sets import encode,bound_model
from verify_target_cover import find_witness
ROOT=Path(__file__).resolve().parent
c=json.loads((ROOT/'replacement_cover.json').read_text())['claims'][6]
m,bound=bound_model(['131'],c);assert bound<Q(str(c['target'][0]))
lo,hi=[Q(str(x))-3 for x in c['target']]
with tempfile.TemporaryDirectory() as tmp:
    exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
    scan=json.loads(subprocess.run([str(exe),'9','250000000'],input=encode(m,['11'],['11'],lo,hi),text=True,capture_output=True,check=True).stdout)
m.radius=2;m.reset='';out={'replaces_claim':7,'forbidden':['131'],'left':['11'],'right':['11'],'sum_target':[str(lo),str(hi)],'dominance_bound':str(bound),'scan':scan,'witnesses':[],'unresolved':[]}
with localcontext() as ctx:
    ctx.prec=80;bd=m.tail_bounds(Decimal,240)
    for k in range(101):
        t=3+lo+(hi-lo)*k/100;found=find_witness(m,dict(center=3,u='11',v='11'),t,bd,budget=100000)
        if found:out['witnesses'].append(found)
        else:out['unresolved'].append(str(t))
if scan['complete'] and not scan['covers_target']:
    from certify_refined_gaps import gaps,exclude
    gs=gaps(dict(scan,target_sum=out['sum_target']))
    a,b=max(gs,key=lambda z:z[1]-z[0]);a,b=(3*a+b)/4,(a+3*b)/4
    out['rigorous_counterexample']={'interval':[str(a),str(b)],'check':exclude(m,['11'],['11'],a,b)}
(ROOT/'kf_cylinder_check.json').write_text(json.dumps(out,indent=2)+'\n')
print('KF[11]+KF[11]',scan['covers_target'],scan['complete'],'points',len(out['witnesses']),'unresolved',len(out['unresolved']))
