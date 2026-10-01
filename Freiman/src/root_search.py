"""Discover initial roots independently of Freiman's root tables.

Floating screening precedes exact spectral bounds. Even the exact conditional
intervals are NOT claimed to belong to M until a closed Lem2 proof is found.
"""
import argparse
import bisect
import json
import math
from functools import lru_cache
from itertools import product
from pathlib import Path
from layout import DATA
from exact_cf import CF, matrix, interval
from obstruction_probe import scan
from menu_search import tails, geometric_holes
from spectral_bounds import bound_root


def apply(word,x):
    a,b,c,d=matrix(word)
    return (a*x+b)/(c*x+d)


def max_value(word,state):
    return apply(word,tails(state)[len(word)%2==0])


@lru_cache(None)
def word_info(word):
    state=scan(word)
    if state is None:return None
    a,b,c,d=matrix(word)
    vals=[(a*x+b)/(c*x+d) for x in tails(state)]
    return min(vals),max(vals),c/d,d,state


def core_max(a,b,center):
    core=tuple(reversed(a))+(center,)+b
    sa,sb=scan(a),scan(b)
    value=0
    for i,d in enumerate(core):
        if i==len(a) or d<=2:continue
        val=d+max_value(tuple(reversed(core[:i])),sa)+max_value(core[i+1:],sb)
        value=max(value,val)
    return value


def discover_roots(depth=9,side_limit=5,lookahead=2,center=4):
    lower,upper=float(CF)-center,math.sqrt(21)-center
    words={n:[w for w in product((1,2,3,4),repeat=n) if word_info(w)]
           for n in range(1,side_limit+1)}
    sorted_words={n:sorted(words[n],key=lambda w:word_info(w)[0]) for n in words}
    lows={n:[word_info(w)[0] for w in sorted_words[n]] for n in words}
    candidates=[];counts={'pairs':0,'core_safe':0,'lookahead_safe':0}
    for total in range(2,depth+1):
        for h in range(1,side_limit+1):
            k=total-h
            if k<h or k>side_limit:continue
            for a in words[h]:
                la,ua,r,qa,sa=word_info(a)
                stop=bisect.bisect_right(lows[k],upper-la)
                for b in sorted_words[k][:stop]:
                    if h==k and b<a:continue
                    lb,ub,s,qb,sb=word_info(b)
                    if ua+ub<lower:continue
                    rho=(qa/qb)**2
                    if not 1/100<=rho<=100:continue
                    counts['pairs']+=1
                    cm=core_max(a,b,center)
                    lo=max(la+lb,cm-center,lower)
                    hi=min(ua+ub,upper)
                    if lo>=hi:continue
                    counts['core_safe']+=1
                    if geometric_holes(sa,sb,h%2,k%2,r,s,rho,lookahead):continue
                    counts['lookahead_safe']+=1
                    candidates.append((lo,hi,a,b,cm))
        print(json.dumps({'total_depth':total,'candidates':len(candidates),'counts':counts}),flush=True)
    # Greedy cover records residual gaps explicitly.
    ordered=sorted(candidates)
    selected=[];gaps=[];end=lower
    while end<upper-1e-14:
        possible=[x for x in ordered if x[0]<=end+1e-14 and x[1]>end+1e-14]
        if possible:
            best=max(possible,key=lambda x:x[1]);selected.append(best);end=best[1]
        else:
            later=[x for x in ordered if x[0]>end+1e-14]
            next_start=min((x[0] for x in later),default=upper)
            gaps.append([end+center,next_start+center]);end=next_start
    return selected,gaps,counts,candidates


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--depth',type=int,default=9)
    p.add_argument('--side-limit',type=int,default=5)
    p.add_argument('--lookahead',type=int,default=2)
    p.add_argument('--center',type=int,default=4)
    p.add_argument('--output',default='root_inventory.json')
    args=p.parse_args()
    selected,gaps,counts,candidates=discover_roots(args.depth,args.side_limit,args.lookahead,args.center)
    checked=[]
    for _,_,a,b,_ in selected:
        data=bound_root(a,b,args.center)
        checked.append(data)
        print('exact spectral bound',data['a'],data['b'],data['conditional_markov_interval_decimal'],flush=True)
    out={'proof_complete':False,'scope':'Root discovery; no interval filling has been certified.',
         'settings':vars(args),'counts':counts,'floating_screen_gaps':gaps,'selected_roots':checked,
         'candidate_roots':[{'a':''.join(map(str,a)),'b':''.join(map(str,b)),
                             'center':args.center,'screen_interval':[lo+args.center,hi+args.center]}
                            for lo,hi,a,b,_ in candidates]}
    (DATA/args.output).write_text(json.dumps(out,indent=2)+'\n')
