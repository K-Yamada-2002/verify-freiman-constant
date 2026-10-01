"""Reject intrinsically gapped roots and replan a conditional initial cover."""
import argparse
import json
import math
from pathlib import Path
from layout import DATA
from exact_cf import K, CF, union
from spectral_bounds import bound_root
from deep_audit import audit_root


def key(row):return row['a'],row['b'],row['center']


def plan(pool,invalid,spectral):
    candidates=[]
    for row in pool.values():
        k=key(row)
        if k in invalid:continue
        iv=spectral[k]['conditional_markov_interval_decimal'] if k in spectral else row['screen_interval']
        if iv and iv[0]<iv[1]:candidates.append((iv[0],iv[1],k))
    chosen=[];gaps=[];end=float(CF);upper=math.sqrt(21)
    while end<upper-1e-14:
        choices=[r for r in candidates if r[0]<=end+1e-14 and r[1]>end+1e-14]
        if choices:
            best=max(choices,key=lambda r:r[1]);chosen.append(best[2]);end=best[1]
        else:
            nxt=min((r[0] for r in candidates if r[0]>end+1e-14),default=upper)
            gaps.append([end,nxt]);end=nxt
    return chosen,gaps


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--depth',type=int,default=7)
    p.add_argument('--max-audits',type=int,default=150)
    p.add_argument('--output',default='refined_roots.json')
    args=p.parse_args();base=DATA
    pool={};spectral={};audits={};invalid=set()
    for name in ['root_inventory_depth11.json','root_inventory_center3.json']:
        inv=json.loads((base/name).read_text())
        for row in inv['candidate_roots']:pool[key(row)]=row
        for row in inv['selected_roots']:spectral[key(row)]=row
    for row in json.loads((base/'root_deep_audit.json').read_text())['records']:
        if row['depth']>=args.depth or row['status']=='certified_intrinsic_gap':
            audits[key(row)]=row
            if row['status']=='certified_intrinsic_gap':invalid.add(key(row))
    attempts=0
    while True:
        selected,gaps=plan(pool,invalid,spectral)
        unresolved=[k for k in selected if k not in audits or k not in spectral]
        if not unresolved or attempts>=args.max_audits:break
        k=unresolved[0];a,b,c=k;aa,bb=tuple(map(int,a)),tuple(map(int,b))
        if k not in audits:
            row={'a':a,'b':b,'center':c,**audit_root(aa,bb,args.depth)}
            audits[k]=row
            if row['status']=='certified_intrinsic_gap':invalid.add(k)
            attempts+=1;print(json.dumps(row),flush=True)
        if k not in invalid and k not in spectral:spectral[k]=bound_root(aa,bb,c)
    selected,gaps=plan(pool,invalid,spectral)
    complete=all(k in spectral and k in audits and audits[k]['status']=='no_gap_detected_through_depth'
                 for k in selected)
    ivs=[tuple(K(*v) for v in spectral[k]['conditional_markov_interval'])
         for k in selected if k in spectral and spectral[k]['conditional_markov_interval']]
    merged=union(ivs)
    connects=complete and len(merged)==1 and merged[0][0]<=CF and merged[0][1]*merged[0][1]>=21
    result={'proof_complete':False,'scope':'Conditional initial cover only. Full-hull filling remains unproved.',
            'audit_depth':args.depth,'new_audits':attempts,'pool_count':len(pool),
            'invalid_roots':[list(k) for k in sorted(invalid)],'audits':list(audits.values()),
            'selected_roots':[spectral[k] for k in selected if k in spectral],
            'unresolved_selected_roots':[list(k) for k in selected if k not in spectral or k not in audits],
            'conditional_cover_verified':connects,'floating_screen_gaps':gaps,
            'exact_conditional_components':[[v.data() for v in iv] for iv in merged],
            'conditional_components_decimal':[[float(v) for v in iv] for iv in merged]}
    (base/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('audits','selected_roots','invalid_roots')},indent=2))
