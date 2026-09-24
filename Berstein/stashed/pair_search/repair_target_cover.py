#!/usr/bin/env python3
"""Fill residual gaps using stronger target-specific safe subshifts."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import time
from target_cover import ThresholdModel,scan,complement,merge


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=Path(__file__).with_name('target_r2_fine.json'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('target_repaired.json'))
    p.add_argument('--radius',type=int,default=3)
    p.add_argument('--epsilon',type=float,default=1e-6)
    p.add_argument('--budget',type=int,default=1000000)
    p.add_argument('--rational-leaves',action='store_true')
    args=p.parse_args();start=time.monotonic()
    data=json.loads(args.input.read_text())
    slabs=list(data['slabs']);covered=merge([z for s in slabs for z in s['covered']])
    original=complement(covered,4.1,4.52);repairs=[]
    for i,(a,b) in enumerate(original):
        lo=max(4.1,a-2*args.epsilon);hi=min(4.52,b+2*args.epsilon)
        H=Q(f'{lo:.14f}')-Q('0.000001')
        m=ThresholdModel(4,args.radius,H)
        s=scan(m,[lo,hi],args.epsilon,args.budget,rational_leaves=args.rational_leaves)
        slab=dict(model=m.metadata(),**s)
        slabs.append(slab);repairs.append(slab);covered=merge(covered+s['covered'])
        print(f'{i+1}/{len(original)} [{a:.12f},{b:.12f}]: {s["status"]}, {len(s["gaps"])} gaps, {len(s["candidates"])} roots',flush=True)
        result=dict(status='finite-scale numerical cover, NOT interval inclusion',source=str(args.input),
                    epsilon=args.epsilon,slabs=slabs,repair_count=len(repairs),covered=covered,
                    gaps=complement(covered,4.1,4.52),elapsed_seconds=time.monotonic()-start)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('remaining gaps',len(complement(covered,4.1,4.52)),flush=True)

if __name__=='__main__':main()
