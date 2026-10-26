"""Targeted initial-root refinement around gaps left by rejecting false hulls."""
import argparse
import json
from pathlib import Path
from layout import DATA
from exact_cf import K, CF, union
from root_search import word_info,core_max
from menu_search import extensions,geometric_holes
from spectral_bounds import bound_root
from deep_audit import audit_root
from refine_roots import key,plan


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=6)
    p.add_argument('--parents',type=int,default=24)
    p.add_argument('--output',default='augmented_roots.json');args=p.parse_args()
    base=DATA
    initial=json.loads((base/'refined_roots.json').read_text())
    components=initial['conditional_components_decimal']
    gaps=[(l[1],r[0]) for l,r in zip(components,components[1:])]
    fullpool={}
    for filename in ['root_inventory_depth11.json','root_inventory_center3.json']:
        for row in json.loads((base/filename).read_text())['candidate_roots']:fullpool[key(row)]=row
    parents=[r for r in fullpool.values() if any(r['screen_interval'][0]<hi and lo<r['screen_interval'][1]
                                               for lo,hi in gaps)]
    parents=sorted(parents,key=lambda r:(len(r['a'])+len(r['b']),-(r['screen_interval'][1]-r['screen_interval'][0])))[:args.parents]
    pool=dict(fullpool)
    for root in parents:
        a,b=tuple(map(int,root['a'])),tuple(map(int,root['b']));center=root['center']
        sa,sb=word_info(a)[4],word_info(b)[4]
        for total in range(1,args.length+1):
            for left_n in range(total+1):
                for ea in extensions(sa,left_n):
                    aa=a+ea[0];la,ua,r,qa,sta=word_info(aa)
                    for eb in extensions(sb,total-left_n):
                        bb=b+eb[0];lb,ub,s,qb,stb=word_info(bb)
                        lo,hi=center+la+lb,center+ua+ub
                        if not any(lo<gh and gl<hi for gl,gh in gaps):continue
                        k=(''.join(map(str,aa)),''.join(map(str,bb)),center)
                        if k in pool:continue
                        rho=(qa/qb)**2
                        if not 1/100<=rho<=100:continue
                        lo=max(lo,core_max(aa,bb,center),float(CF))
                        if lo>=hi:continue
                        if geometric_holes(sta,stb,len(aa)%2,len(bb)%2,r,s,rho,3):continue
                        pool[k]={'a':k[0],'b':k[1],'center':center,'screen_interval':[lo,hi]}
        print('expanded parent',key(root),'pool',len(pool),flush=True)
    spectral={key(r):r for r in initial['selected_roots']}
    audits={key(r):r for r in initial['audits']}
    invalid={tuple(k) for k in initial['invalid_roots']}
    for iteration in range(151):
        selected,screen_gaps=plan(pool,invalid,spectral)
        need=[k for k in selected if k not in audits or k not in spectral]
        if not need:break
        a,b,c=k=need[0];aa,bb=tuple(map(int,a)),tuple(map(int,b))
        if k not in audits:
            result={'a':a,'b':b,'center':c,**audit_root(aa,bb,7)}
            audits[k]=result
            if result['status']=='certified_intrinsic_gap':invalid.add(k)
            print(json.dumps(result),flush=True)
        if k not in invalid and k not in spectral:spectral[k]=bound_root(aa,bb,c)
    selected,screen_gaps=plan(pool,invalid,spectral)
    ivs=[tuple(K(*v) for v in spectral[k]['conditional_markov_interval']) for k in selected
         if k in spectral and spectral[k]['conditional_markov_interval']]
    merged=union(ivs)
    audited=all(k in spectral and k in audits and audits[k]['status']=='no_gap_detected_through_depth'
                for k in selected)
    connects=audited and len(merged)==1 and merged[0][0]<=CF and merged[0][1]*merged[0][1]>=21
    result={'proof_complete':False,'scope':'Conditional initial cover; every selected full hull still requires Lem2.',
            'settings':vars(args),'pool_count':len(pool),'audits':list(audits.values()),
            'invalid_roots':[list(k) for k in sorted(invalid)],
            'selected_roots':[spectral[k] for k in selected if k in spectral],
            'conditional_cover_verified':connects,'all_selected_audited':audited,
            'floating_screen_gaps':screen_gaps,
            'exact_conditional_components':[[v.data() for v in iv] for iv in merged],
            'conditional_components_decimal':[[float(v) for v in iv] for iv in merged]}
    (base/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print('conditional cover verified',connects, 'roots',len(selected),'gaps',screen_gaps,flush=True)
