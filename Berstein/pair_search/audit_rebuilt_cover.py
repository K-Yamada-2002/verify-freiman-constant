#!/usr/bin/env python3
"""Exact dominance and high precision stress tests of the replacement cover."""
import argparse,json
from decimal import Decimal,localcontext
from fractions import Fraction as Q
from pathlib import Path
from verify_reduced import inspect
from verify_target_cover import find_witness,certify
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,default=ROOT/'rebuilt_cover.json');p.add_argument('--output',type=Path,default=ROOT/'rebuilt_audit.json');p.add_argument('--points',type=int,default=101);args=p.parse_args()
    data=json.loads(args.input.read_text())
    assert len(data['claims'])==11
    assert all(c['scan']['complete'] and c['scan']['covers_target'] for c in data['claims'])
    models,definitions,reports=inspect(data)
    # Old failure intervals' endpoints, quarter points and midpoint: these are
    # additional stress points, not a replacement for the whole-interval scan.
    old=json.loads((ROOT/'refined_gap_certificates.json').read_text())
    old.append(json.loads((ROOT/'rejected_second_gap.json').read_text()))
    critical=set()
    for gap in old:
        a,b=map(Q,gap['excluded_closed_interval'])
        critical.update(3+a+(b-a)*k/4 for k in range(5))
    critical.update(3+Q(x) for x in ['1.12476988','1.17306081','1.367178913','1.38221501'])
    witnesses=[];unresolved=[];bds={};expected=0;critical_checked=set()
    with localcontext() as ctx:
        ctx.prec=80
        for i,c in enumerate(data['claims']):
            m=models[c['graph']];lo,hi=map(lambda x:Q(str(x)),c['target'])
            targets={lo+(hi-lo)*k/(args.points-1) for k in range(args.points)}
            extra={t for t in critical if lo<=t<=hi};targets|=extra;critical_checked|=extra;expected+=len(targets)
            if c['graph'] not in bds:bds[c['graph']]=m.tail_bounds(Decimal,240)
            bd=bds[c['graph']]
            for t in sorted(targets):
                td=Decimal(t.numerator)/Decimal(t.denominator)-3
                offers=[]
                for u in c['left']:
                    for v in c['right']:
                        x,y=m.cylinder(u,bd),m.cylinder(v,bd)
                        if x[3]+y[3]<=td<=x[4]+y[4]:offers.append((min(td-x[3]-y[3],x[4]+y[4]-td),u,v))
                found=None
                for _,u,v in sorted(offers,reverse=True):
                    found=find_witness(m,dict(center=3,u=u,v=v),t,bd,budget=100000)
                    if found:break
                if found:found.update(claim=i+1,old_gap_stress=t in critical);witnesses.append(found)
                else:unresolved.append(dict(claim=i+1,target=str(t),old_gap_stress=t in critical))
            print('claim',i+1,'witnesses',len(witnesses),'unresolved',len(unresolved),flush=True)
    assert critical_checked==critical
    # Replay every periodic witness using rational backward CF evaluation.
    for w in witnesses:
        c=data['claims'][w['claim']-1];m=models[c['graph']]
        a,b=certify(m,w['u'],w['root_u']);e,f=certify(m,w['v'],w['root_v']);t=Q(w['target'])
        error=max(abs(3+a+e-t),abs(3+b+f-t))
        assert error==Q(w['error_bound']) and error<Q(1,10**30)
    assert len(witnesses)+len(unresolved)==expected
    result=dict(status='Finite-scale and point evidence only, NOT interval inclusion',source=str(args.input),definitions=definitions,claims=reports,
                old_gap_stress_points=len(critical),expected=expected,witnesses=witnesses,unresolved=unresolved)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('TOTAL',expected,'unresolved',len(unresolved),flush=True)
if __name__=='__main__':main()
