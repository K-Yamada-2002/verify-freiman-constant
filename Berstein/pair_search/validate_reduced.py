#!/usr/bin/env python3
"""Validate the small cover with each K+L product checked independently."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import time
from reduce_cover import scan_product,dominance,background,same_language
from target_cover import ThresholdModel,merge,complement


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=Path(__file__).with_name('reduced_search.json'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('reduced_validation.json'))
    p.add_argument('--epsilon',type=float,default=1e-6)
    p.add_argument('--rational-leaves',action='store_true')
    p.add_argument('--patch',type=Path)
    p.add_argument('--merge-equivalent',action='store_true')
    args=p.parse_args()
    if args.merge_equivalent and not args.patch:p.error('--merge-equivalent requires --patch')
    data=json.loads(args.input.read_text());selected=data['selected'];start=time.monotonic()
    cuts=[4.1]+[round((a['interval'][1]+b['interval'][0])/2,6) for a,b in zip(selected,selected[1:])]+[4.52]
    jobs=[];merge_audit=None
    for i,item in enumerate(selected):
        if args.merge_equivalent and i==5:continue
        c=data['products'][item['product']]
        target=[cuts[i] if i==0 else round(cuts[i]-1e-6,6),cuts[i+1] if i==len(selected)-1 else round(cuts[i+1]+1e-6,6)]
        if target[0]<item['interval'][0] or target[1]>item['interval'][1]:raise ValueError('Rounded target outside initial component')
        if args.patch and i==4:
            patch=json.loads(args.patch.read_text())
            jobs.append((item['product'],c,[target[0],4.235001]))
            if args.merge_equivalent:
                following=data['products'][selected[i+1]['product']]
                ms=[]
                for spec in (patch['model'],following['model']):
                    ms.append(ThresholdModel(spec['digits'],spec['radius'],spec['threshold']))
                equal,states=same_language(*ms)
                if not equal:raise ValueError('Cannot merge distinct Cantor sets')
                merge_audit=dict(equivalent=True,visited_state_pairs=states,models=[m.metadata() for m in ms])
                patch=dict(patch,left=following['left'],right=following['right'])
                jobs.append((-2,patch,[4.234999,round(cuts[i+2]+1e-6,6)]))
            else:jobs.append((-1,patch,[4.234999,target[1]]))
        else:jobs.append((item['product'],c,target))
    claims=[];models={}
    for i,(product_id,c,target) in enumerate(jobs):
        spec=c['model'];sig=c['graph']
        if sig not in models:
            m=ThresholdModel(spec['digits'],spec['radius'],spec['threshold'])
            bg=background(m)
            # Choose a simpler rational threshold retaining every core edge,
            # without adding any edge that was absent at the old threshold.
            for places in range(2,13):
                scale=10**places;z=bg*scale;H=Q(-(-z.numerator//z.denominator),scale)
                if H<=m.threshold:
                    simpler=ThresholdModel(m.digits,m.radius,H)
                    if simpler.graph_signature!=sig:raise ValueError('Changed graph during threshold simplification')
                    m=simpler;break
            models[sig]=m
        m=models[sig]
        bound=max(background(m),dominance(m,tuple(c['left']),tuple(c['right'])))
        if Q(str(target[0]))<=bound:raise ValueError('Invalid Perron dominance')
        result=scan_product(m,c['left'],c['right'],target,args.epsilon,3000000,args.rational_leaves)
        claims.append(dict(product=product_id,model=m.metadata(),graph=sig,left=c['left'],right=c['right'],target=target,dominance_bound=str(bound),**result))
        print(i+1,target,len(result['gaps']),'gaps',result['visited'],'nodes',flush=True)
        out=dict(status='Numerical candidates only; NOT interval inclusion',merge_audit=merge_audit,epsilon=args.epsilon,claims=claims,
                 gaps=complement([z for c in claims for z in c['covered']],4.1,4.52),elapsed_seconds=time.monotonic()-start)
        args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('global gaps',len(out['gaps']),flush=True)

if __name__=='__main__':main()
