#!/usr/bin/env python3
"""Simplify by deleting forbidden reversal pairs while retaining dominance.

Deleting rules enlarges the sum, so earlier finite-distance covers transfer
without a fresh billion-node scan. All newly admitted cross pairs are checked.
"""
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from search import Model
from reduce_cover import dominance
ROOT=Path(__file__).resolve().parent
S=10**15

def bound_model(words,c):
    m=Model('simple','123',words);m.digits=3;m.radius=4;m.cert_bounds=m.tail_bounds(Q,16)
    bound=max(m.background(4)[0],dominance(m,tuple(c['left']),tuple(c['right'])))
    return m,bound

def encode(m,left,right,lo,hi):
    bounds=m.tail_bounds(Q,40);ids={s:i for i,s in enumerate(m.states)}
    rows=[f'{len(ids)} {int(Q(lo)*S)} {int(Q(hi)*S)}']
    for s in m.states:
        a,b=bounds[s];edges=dict(m.edges[s]);rows.append(' '.join(map(str,[int(a*S),-int((-b*S)//1)]+[ids[edges[k]] if k in edges else -1 for k in '123'])))
    for factor in (left,right):rows.append(str(len(factor)));rows.extend(factor)
    return '\n'.join(rows)+'\n'

def main():
    data=json.loads((ROOT/'replacement_cover.json').read_text());defs={d['graph']:d for d in data['definitions']};out={'claims':[]}
    for i,c in enumerate(data['claims'],1):
        original=defs[c['graph']]['forbidden'];words=set(original);floor=Q(str(c['target'][0]));attempts=[]
        # Greedy deletions prioritize long words; no minimality claim.
        groups=sorted({tuple(sorted({w,w[::-1]})) for w in words},key=lambda g:(-max(map(len,g)),g))
        for group in groups:
            proposed=words-set(group);m,b=bound_model(proposed,c)
            ok=b<floor
            attempts.append({'removed':group,'upper':str(b),'accepted':ok})
            if ok:words=proposed
        m,b=bound_model(words,c)
        out['claims'].append({'claim':i,'old_forbidden':original,'forbidden':sorted(words),'new_upper':str(b),'passes':b<floor,'target':c['target'],'left':c['left'],'right':c['right'],'attempts':attempts})
        print(i,len(original),'->',len(words),'upper',float(b),'passes',b<floor,flush=True)
        (ROOT/'simplified_sets.json').write_text(json.dumps(out,indent=2)+'\n')
    kf=Model('KF','123',('131',));inp=encode(kf,['1','2','3'],['1','2','3'],'1.244445','1.52')
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
        scan=json.loads(subprocess.run([str(exe),'6','20000000'],input=inp,text=True,capture_output=True,check=True).stdout)
    out['kf_sum_scan']={'sum_target':['1.244445','1.52'],'scan':scan}
    (ROOT/'simplified_sets.json').write_text(json.dumps(out,indent=2)+'\n')
    print('KF',scan['covers_target'],scan['complete'],len(scan['covered']),flush=True)
if __name__=='__main__':main()
