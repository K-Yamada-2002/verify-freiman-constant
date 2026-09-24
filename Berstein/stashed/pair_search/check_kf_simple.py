#!/usr/bin/env python3
"""Check a simple KF+KF candidate and a rigorous obstruction to full replacement."""
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from search import Model
from simple_sets import encode,bound_model
from certify_refined_gaps import exclude
ROOT=Path(__file__).resolve().parent
m=Model('KF','123',('131',));out={}
# A closed interval inside a gap in the coarse whole-set scan.
a,b=Q('1.3720'),Q('1.3727')
out['excluded_closed_interval']=[str(a),str(b)]
out['exclusion']=exclude(m,['1','2','3'],['1','2','3'],a,b)
print('KF exclusion',out['exclusion'],flush=True)
with tempfile.TemporaryDirectory() as tmp:
    exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
    inp=encode(m,['1','2','3'],['1','2','3'],'1.27','1.36')
    scan=json.loads(subprocess.run([str(exe),'8','200000000'],input=inp,text=True,capture_output=True,check=True).stdout)
    out['candidate']={'sum_interval':['1.27','1.36'],'scan':scan,'dominance_threshold':'191/45'}
    print('KF candidate',scan['covers_target'],scan['complete'],len(scan['covered']),flush=True)
# Evaluate KF with the old roots; inclusion is NOT inferred for smaller sets.
data=json.loads((ROOT/'replacement_cover.json').read_text())
out['same_roots_dominance']=[]
for i,c in enumerate(data['claims'],1):
    illegal=[w for side in ('left','right') for w in c[side] if m.follow(w) is None]
    if illegal:
        out['same_roots_dominance'].append({'claim':i,'illegal_prefixes':illegal});continue
    model,bound=bound_model(['131'],c)
    out['same_roots_dominance'].append({'claim':i,'upper':str(bound),'passes':bound<Q(str(c['target'][0]))})
from decimal import Decimal,localcontext
from verify_target_cover import find_witness
m.digits=3;m.radius=2;m.reset=''
witnesses=[];unresolved=[]
with localcontext() as ctx:
    ctx.prec=80;bd=m.tail_bounds(Decimal,240)
    for k in range(101):
        target=Q('4.27')+Q('0.09')*k/100;found=None
        for u in '123':
            for v in '123':
                found=find_witness(m,dict(center=3,u=u,v=v),target,bd,budget=100000)
                if found:break
            if found:break
        if found:witnesses.append(found)
        else:unresolved.append(str(target))
out['candidate']['witnesses']=witnesses;out['candidate']['unresolved']=unresolved
(ROOT/'kf_simple_check.json').write_text(json.dumps(out,indent=2)+'\n')
