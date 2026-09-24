#!/usr/bin/env python3
"""Independent checks for every reduced single-product candidate."""
import argparse
from decimal import Decimal,localcontext
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import time
from reduce_cover import dominance,background,same_language
from target_cover import ThresholdModel,complement
from verify_target_cover import find_witness,certify


def forbidden_words(m):
    """Minimal forbidden words for the finite-memory core, not sampled rules."""
    alphabet=''.join(a for a in m.alphabet if m.follow(a) is not None)
    forbidden=[]
    for n in range(1,2*m.radius+2):
        for p in product(alphabet,repeat=n):
            w=''.join(p)
            if any(f in w for f in forbidden):continue
            if m.follow(w) is None:forbidden.append(w)
    return alphabet,forbidden


def inspect(data):
    models={};definitions=[];reports=[]
    for i,c in enumerate(data['claims']):
        sig=c['graph'];spec=c['model']
        if sig not in models:
            m=ThresholdModel(spec['digits'],spec['radius'],spec['threshold'])
            if m.graph_signature!=sig:raise ValueError('Incorrect graph')
            models[sig]=m
            alphabet,forbidden=forbidden_words(m)
            definitions.append(dict(label=chr(65+len(definitions)),graph=sig,model=spec,
                                    alphabet=alphabet,forbidden=forbidden))
        m=models[sig]
        bound=max(background(m),dominance(m,tuple(c['left']),tuple(c['right'])))
        if bound!=Q(c['dominance_bound']):raise ValueError('Incorrect dominance bound')
        a,b=map(lambda x:Q(str(x)),c['target'])
        if bound>=a:raise ValueError('Dominance not valid on assigned interval')
        q=c['rational_leaf_check']
        intervals=[tuple(map(Q,z)) for z in q['covered']]
        gaps=complement(intervals,a,b)
        width=Q(q['maximum_width']);margin=a-bound-width
        if gaps or width>Q('0.000001') or margin<=0:raise ValueError('Failed rational finite-scale cover')
        reports.append(dict(claim=i+1,label=next(d['label'] for d in definitions if d['graph']==sig),
                            left=c['left'],right=c['right'],target=[str(a-3),str(b-3)],
                            dominance_bound=str(bound),maximum_width=str(width),lagrange_margin=str(margin)))
    if data.get('merge_audit'):
        recorded=data['merge_audit'];pair=[]
        for spec in recorded['models']:
            pair.append(ThresholdModel(spec['digits'],spec['radius'],spec['threshold']))
        equal,states=same_language(*pair)
        if not equal or states!=recorded['visited_state_pairs']:raise ValueError('Incorrect language-equivalence record')
    allgaps=complement([tuple(Q(x)+3 for x in r['target']) for r in reports],Q('4.1'),Q('4.52'))
    if allgaps:raise ValueError('Claim intervals do not cover the target')
    return models,definitions,reports


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=Path(__file__).with_name('reduced_final.json'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('reduced_audit.json'))
    p.add_argument('--points',type=int,default=101)
    p.add_argument('--replay',type=Path)
    args=p.parse_args();start=time.monotonic()
    if args.points<2:p.error('points must be >= 2')
    data=json.loads(args.input.read_text());models,defs,reports=inspect(data)
    if args.replay:
        saved=json.loads(args.replay.read_text())
        if saved['definitions']!=defs or saved['claims']!=reports:raise ValueError('Metadata mismatch')
        n=saved['points_per_claim'];expected=set()
        for i,c in enumerate(data['claims']):
            a,b=map(lambda x:Q(str(x)),c['target'])
            expected.update((i,str(a+(b-a)*k/(n-1))) for k in range(n))
        actual=[(w['claim'],w['target']) for w in saved['witnesses']]+[(w['claim'],w['target']) for w in saved['unresolved']]
        if len(actual)!=len(expected) or set(actual)!=expected:raise ValueError('Missing/duplicate target')
        for w in saved['witnesses']:
            c=data['claims'][w['claim']];m=models[c['graph']]
            if w['root_u'] not in c['left'] or w['root_v'] not in c['right'] or w['center']!=3:raise ValueError('Incorrect factors')
            a,b=certify(m,w['u'],w['root_u']);e,f=certify(m,w['v'],w['root_v']);t=Q(w['target'])
            error=max(abs(3+a+e-t),abs(3+b+f-t))
            if error!=Q(w['error_bound']) or error>=Q(1,10**30):raise ValueError('Bad witness')
        print('Replayed',len(saved['witnesses']),'rational point witnesses and',len(reports),'dominance/aggregate checks')
        return
    witnesses=[];unresolved=[];bounds={}
    with localcontext() as ctx:
        ctx.prec=75
        for i,c in enumerate(data['claims']):
            m=models[c['graph']]
            if c['graph'] not in bounds:bounds[c['graph']]=m.tail_bounds(Decimal,240)
            bd=bounds[c['graph']];a,b=map(lambda x:Q(str(x)),c['target'])
            for k in range(args.points):
                t=a+(b-a)*k/(args.points-1);td=Decimal(t.numerator)/Decimal(t.denominator)-3
                offers=[]
                for u in c['left']:
                    for v in c['right']:
                        x,y=m.cylinder(u,bd),m.cylinder(v,bd)
                        if x[3]+y[3]<=td<=x[4]+y[4]:
                            offers.append((min(td-x[3]-y[3],x[4]+y[4]-td),u,v))
                found=None
                for _,u,v in sorted(offers,reverse=True):
                    found=find_witness(m,dict(center=3,u=u,v=v),t,bd,budget=50000)
                    if found:break
                if found:found['claim']=i;witnesses.append(found)
                else:unresolved.append(dict(claim=i,target=str(t)))
            print('claim',i+1,'/',len(reports),'points checked; unresolved',len(unresolved),flush=True)
    result=dict(status='All statements remain unproved interval-inclusion candidates',
                source=str(args.input),definitions=defs,claims=reports,points_per_claim=args.points,
                witnesses=witnesses,unresolved=unresolved,elapsed_seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('witnesses',len(witnesses),'unresolved',len(unresolved),flush=True)

if __name__=='__main__':main()
