#!/usr/bin/env python3
"""Probe near a periodic extreme without enumerating the entire deep tree.

For each nested extreme cylinder, all outside completions are bounded at their
first differing digit. A gap inside the nested product is a root gap ONLY when
it also lies above the outside cap (or below the outside floor).
"""
from pathlib import Path
import sys,json,argparse,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'schecker_generalized'))
import explore as e

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)

def outside_bound(base,extension,high):
    candidates=[];prefix=base
    for digit in extension:
        for alt in '123':
            if alt==digit or '31313' in prefix+alt:continue
            lo,hi=e.cylinder(prefix+alt)
            candidates.append((hi if high else lo,prefix+alt))
        prefix+=digit
    return (max(candidates) if high else min(candidates)) if candidates else None

def nested_prefix(base,high,cycles):
    tail_high=high if len(base)%2==0 else not high
    _,pre,period=e.extreme_tail(e.state_of(base),tail_high)
    return pre+period*cycles

def probe(n,cycles,depth,high):
    root=('3211'+'313121'*n+'3','4322'+'313121'*n)
    ext=tuple(nested_prefix(w,high,cycles) for w in root)
    pair=tuple(w+t for w,t in zip(root,ext))
    rh=[e.cylinder(w) for w in root]
    outside=[outside_bound(w,t,high) for w,t in zip(root,ext)]
    caps=[bound[0]+rh[1-i][int(high)] for i,bound in enumerate(outside) if bound]
    cap=(max(caps) if high else min(caps)) if caps else None
    comp=e.outer_components(*pair,depth)
    gaps=list(e.gaps(comp)); eligible=[]
    for lo,hi in gaps:
        a=max(lo,cap) if high and cap is not None else lo
        b=min(hi,cap) if not high and cap is not None else hi
        if a<b:eligible.append((a,b))
    return dict(root=root,cycles=cycles,depth=depth,high=high,extensions=ext,pair=pair,
        outside_bound=cap.record() if cap else None,local_gaps=len(gaps),
        root_gaps=[e.interval_record(z) for z in eligible],
        scope='Root gaps exclude all outside completions by first-divergence bounds; local gaps alone are not root gaps')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=0);ap.add_argument('--max-cycles',type=int,default=3)
    ap.add_argument('--depth',type=int,default=3);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    rows=[];start=time.monotonic()
    for high in (False,True):
        for cycles in range(a.max_cycles+1):
            row=probe(a.n,cycles,a.depth,high);rows.append(row)
            print('high',high,'cycles',cycles,'local gaps',row['local_gaps'],'root gaps',len(row['root_gaps']),flush=True)
            a.output.write_text(json.dumps(dict(status='BOUNDED_EXACT_PROBE',rows=rows,seconds=time.monotonic()-start),indent=2)+'\n')
