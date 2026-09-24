#!/usr/bin/env python3
"""Audit rational dominance, proposed cover, and periodic point witnesses.

Cover audit checks the proposed intervals' union, NOT their containment in
Cantor sums. Periodic approximants certify errors, NOT exact membership.
"""
import argparse
from decimal import Decimal,localcontext
from fractions import Fraction as Q
import json
from pathlib import Path
import time
from target_cover import ThresholdModel,near_bounds,rational_bounds,merge,complement


def certify(m,word,prefix):
    if not word.startswith(prefix) or m.follow(word) is None or m.follow(word+'2'*(2*m.radius+1))!=m.reset:
        raise ValueError('Illegal periodic witness')
    return rational_bounds(word+'2'*100,m.digits)


def find_witness(m,c,target,bounds,budget=20000,exponent=30):
    t=Decimal(target.numerator)/Decimal(target.denominator)-c['center']
    eps=Decimal(10)**(-exponent)
    stack=[(m.cylinder(c['u'],bounds),m.cylinder(c['v'],bounds))];visited=0
    while stack and visited<budget:
        x,y=stack.pop();visited+=1
        lo,hi=x[3]+y[3],x[4]+y[4]
        if not lo<=t<=hi:continue
        if hi-lo<eps/4:
            u=x[0]+m.connectors[x[1]];v=y[0]+m.connectors[y[1]]
            a,b=certify(m,u,c['u']);d,e=certify(m,v,c['v'])
            error=max(abs(c['center']+a+d-target),abs(c['center']+b+e-target))
            if error>=Q(1,10**exponent):raise ValueError('Witness precision failure')
            return dict(target=str(target),center=c['center'],root_u=c['u'],root_v=c['v'],u=u,v=v,error_bound=str(error),visited=visited)
        if x[4]-x[3]>=y[4]-y[3]:pairs=[(z,y) for z in m.children(x,bounds)]
        else:pairs=[(x,z) for z in m.children(y,bounds)]
        pairs=[(a,b) for a,b in pairs if a[3]+b[3]<=t<=a[4]+b[4]]
        pairs.sort(key=lambda ab:min(t-ab[0][3]-ab[1][3],ab[0][4]+ab[1][4]-t))
        stack.extend(pairs)
    return None


def audit(data):
    models={};entries=[];intervals=[]
    for index,s in enumerate(data['slabs']):
        spec=s['model'];key=(spec['digits'],spec['radius'],spec['threshold'])
        if key not in models:models[key]=ThresholdModel(*key)
        m=models[key]
        if m.metadata()!=spec:raise ValueError('Model definition/count mismatch')
        if m.threshold>=Q(str(s['target'][0])):raise ValueError('Threshold not below target')
        for c in s['candidates']:
            if min(len(c['u']),len(c['v']))<m.radius:raise ValueError('Short root')
            _,hi=near_bounds(c['u'],c['v'],c['center'],m.radius,m.digits,True,m)
            if hi!=Q(c['near_bound']) or hi>m.threshold:raise ValueError('Near-center bound mismatch')
            for a,b in c['intervals']:
                a,b=Q(str(a)),Q(str(b))
                if not Q(str(s['target'][0]))<=a<=b<=Q(str(s['target'][1])):raise ValueError('Interval outside assigned target')
                intervals.append((a,b));entries.append((a,b,index,key,c))
        if index%10==0: print(f'audit {index+1}/{len(data["slabs"])} models',flush=True)
    union=merge(intervals);gaps=complement(union,Q('4.1'),Q('4.52'))
    rational_checks=[s.get('rational_leaf_check') for s in data['slabs']]
    rational_summary=None
    if all(rational_checks):
        qintervals=[tuple(map(Q,z)) for check in rational_checks for z in check['covered']]
        qgaps=complement(qintervals,Q('4.1'),Q('4.52'))
        maximum=max(Q(c['maximum_sum_hull_width']) for c in rational_checks)
        # Every actual point of each leaf hull is then above its background
        # bound whenever that leaf contributes to its assigned target.
        margins=[Q(str(s['target'][0]))-Q(s['model']['threshold'])-Q(s['rational_leaf_check']['maximum_sum_hull_width']) for s in data['slabs']]
        rational_summary=dict(complete=not qgaps,gaps=[[str(a),str(b)] for a,b in qgaps],
            maximum_sum_hull_width=str(maximum),maximum_sum_hull_width_decimal=float(maximum),
            minimum_lagrange_margin=str(min(margins)),all_leaf_points_above_background=min(margins)>0,
            meaning='Runtime rational leaf enclosures give finite distance bounds, NOT interval inclusion; replaying the stored aggregates alone does not replay all leaves')
    return models,entries,dict(rational_leaf_summary=rational_summary,proposed_cover_complete=not gaps,
                              proposed_gaps=[[str(a),str(b)] for a,b in gaps],
                              distinct_models=len(models),distinct_symbolic_graphs=len({m.graph_signature for m in models.values()}),root_pairs=sum(len(s['candidates']) for s in data['slabs']),
                              candidate_intervals=len(intervals),
                              warning='The proposed intervals cover the target; Cantor-sum interval containment is NOT certified')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=Path(__file__).with_name('target_complete.json'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('target_audit.json'))
    p.add_argument('--replay',type=Path)
    p.add_argument('--refresh-summary',action='store_true')
    args=p.parse_args();start=time.monotonic();data=json.loads(args.input.read_text())
    models,entries,report=audit(data)
    if args.replay:
        saved=json.loads(args.replay.read_text())
        for k in ('proposed_cover_complete','proposed_gaps','distinct_models','root_pairs','candidate_intervals'):
            if saved[k]!=report[k]:raise ValueError('Audit metadata mismatch')
        expected={Q('4.1')+Q(k,1000) for k in range(421)}
        for slab in data['slabs'][42:]:
            a,b=map(lambda x:Q(str(x)),slab['target']);expected.update((a,(a+b)/2,b))
        actual=[Q(w['target']) for w in saved['witnesses']]+list(map(Q,saved['unresolved']))
        if len(actual)!=len(expected) or set(actual)!=expected or saved['target_count']!=len(expected):
            raise ValueError('Missing or duplicate targets')
        for w in saved['witnesses']:
            roots={(c['center'],c['u'],c['v']) for c in data['slabs'][w['slab']]['candidates']}
            if (w['center'],w['root_u'],w['root_v']) not in roots:raise ValueError('Wrong witness root')
            spec=data['slabs'][w['slab']]['model'];m=models[(spec['digits'],spec['radius'],spec['threshold'])]
            a,b=certify(m,w['u'],w['root_u']);c,d=certify(m,w['v'],w['root_v']);t=Q(w['target'])
            error=max(abs(w['center']+a+c-t),abs(w['center']+b+d-t))
            if error!=Q(w['error_bound']) or error>=Q(1,10**30):raise ValueError('Invalid witness')
        print(f'Replayed {len(saved["witnesses"])} rational witnesses and all dominance bounds')
        print(report)
        if args.refresh_summary:
            saved.update(report)
            args.replay.write_text(json.dumps(saved,indent=2)+'\n')
        return
    # Entire target grid plus every adaptive repair's endpoints and midpoint.
    targets={Q('4.1')+Q(k,1000) for k in range(421)}
    for s in data['slabs'][42:]:
        a,b=map(lambda x:Q(str(x)),s['target']);targets.update((a,(a+b)/2,b))
    witnesses=[];unresolved=[];decimal_bounds={}
    with localcontext() as ctx:
        ctx.prec=75
        for i,t in enumerate(sorted(targets)):
            offers=[e for e in entries if e[0]<=t<=e[1]]
            offers.sort(key=lambda e:-(e[1]-e[0]))
            found=None
            for a,b,index,key,c in offers[:8]:
                m=models[key]
                graph=m.graph_signature
                if graph not in decimal_bounds:decimal_bounds[graph]=m.tail_bounds(Decimal,240)
                found=find_witness(m,c,t,decimal_bounds[graph])
                if found:
                    found['slab']=index;break
            if found:witnesses.append(found)
            else:unresolved.append(str(t))
            if (i+1)%50==0:print(f'points {i+1}/{len(targets)}: {len(unresolved)} unresolved',flush=True)
    report.update(source=str(args.input),target_count=len(targets),witnesses=witnesses,unresolved=unresolved,elapsed_seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print({k:v for k,v in report.items() if k!='witnesses'})

if __name__=='__main__':main()
