"""Short Lem2-menu discovery with exact checks for every reported local cover.

Finite-depth lookahead is a heuristic filter, NOT an admissibility theorem.
An unresolved frontier is deliberately retained and proof_complete is false.
"""
import argparse
import json
import math
import numpy as np
from collections import deque
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from layout import DATA
from exact_cf import interval, parameters, tail_endpoint, union
from obstruction_probe import scan, step, DIGITS


@lru_cache(None)
def tails(state):
    return float(tail_endpoint(state,True)),float(tail_endpoint(state,False))


@lru_cache(None)
def extensions(state, length):
    if length==0:
        return (((), state, (1,0,0,1)),)
    out=[]
    for word,st,(a,b,c,d) in extensions(state,length-1):
        for digit in DIGITS:
            nxt=step(st,digit)
            if nxt is not None:
                out.append((word+(digit,),nxt,(b,a+digit*b,d,c+digit*d)))
    return tuple(out)


def branch(r, parity, data):
    word,st,(a,b,c,d)=data
    endpoints=[]
    for t in tails(st):
        x=(a*t+b)/(c*t+d)
        endpoints.append((-1 if parity else 1)*x/(1+r*x))
    return (min(endpoints),max(endpoints)), ((c+r*a)/(d+r*b)), (d+r*b)


def merge_float(intervals):
    result=[]
    for lo,hi in sorted(intervals):
        if result and lo<=result[-1][1]+1e-13:
            result[-1]=(result[-1][0],max(result[-1][1],hi))
        else:
            result.append((lo,hi))
    return result


def geometric_holes_scalar(sa,sb,pa,pb,r,s,rho,depth):
    aa=[branch(r,pa,e)[0] for e in extensions(sa,depth)]
    bb=[branch(s,pb,e)[0] for e in extensions(sb,depth)]
    cover=merge_float((lo+rho*ll,hi+rho*hh) for lo,hi in aa for ll,hh in bb)
    return len(cover)>1


@lru_cache(None)
def cylinder_array(state,depth):
    values=[]
    for _,st,(a,b,c,d) in extensions(state,depth):
        values.append(sorted((a*t+b)/(c*t+d) for t in tails(st)))
    return np.asarray(values)


def geometric_holes(sa,sb,pa,pb,r,s,rho,depth):
    if depth<=1:return geometric_holes_scalar(sa,sb,pa,pb,r,s,rho,depth)
    xa=cylinder_array(sa,depth);xb=cylinder_array(sb,depth)
    aa=xa/(1+r*xa);bb=xb/(1+s*xb)
    if pa:aa=-aa[:,::-1]
    if pb:bb=-bb[:,::-1]
    lo=(aa[:,None,0]+rho*bb[None,:,0]).ravel()
    hi=(aa[:,None,1]+rho*bb[None,:,1]).ravel()
    order=np.argsort(lo)
    return bool(np.any(lo[order][1:]>np.maximum.accumulate(hi[order])[:-1]+1e-13))


def discover(a,b,max_length=4,lookahead=2,ratio_bound=16):
    rr,ss,rhor=parameters(a,b)
    r,s,rho=map(float,(rr,ss,rhor))
    sa,sb,pa,pb=scan(a),scan(b),len(a)%2,len(b)%2
    if geometric_holes(sa,sb,pa,pb,r,s,rho,lookahead):
        return {'status':'intrinsic_gap_detected_numerically','menu':None}
    parent_a=branch(r,pa,extensions(sa,0)[0])[0]
    parent_b=branch(s,pb,extensions(sb,0)[0])[0]
    pl=parent_a[0]+rho*parent_b[0]
    pu=parent_a[1]+rho*parent_b[1]
    candidates=[]
    for total in range(1,max_length+1):
        for left_len in range(total+1):
            right_len=total-left_len
            for ea in extensions(sa,left_len):
                ia,ra,qa=branch(r,pa,ea)
                for eb in extensions(sb,right_len):
                    ib,rb,qb=branch(s,pb,eb)
                    rhoc=rho*(qa/qb)**2
                    if not 1/ratio_bound<=rhoc<=ratio_bound:
                        continue
                    if geometric_holes(ea[1],eb[1],(pa+left_len)%2,(pb+right_len)%2,
                                       ra,rb,rhoc,lookahead):
                        continue
                    candidates.append((ia[0]+rho*ib[0],ia[1]+rho*ib[1],ea[0],eb[0]))
        # Find a minimum-cardinality interval cover at this depth cutoff.
        remaining=sorted(candidates)
        chosen=[]
        frontier=pl
        while frontier<pu-1e-12:
            choices=[c for c in remaining if c[0]<=frontier+1e-12 and c[1]>frontier+1e-12]
            if not choices:break
            best=max(choices,key=lambda c:c[1])
            chosen.append(best)
            frontier=best[1]
        if frontier>=pu-1e-12:
            exact=[interval(a+u,b+w) for _,_,u,w in chosen]
            merged=union(exact)
            parent=interval(a,b)
            if len(merged)==1 and merged[0]==parent:
                return {'status':'exact_local_cover','first_total_length':total,
                        'menu':[[list(u),list(w)] for _,_,u,w in chosen],
                        'candidate_count':len(candidates)}
            # Discovery tolerances are never accepted as a proof of contact.
    return {'status':'no_cover_within_limits','menu':None,'candidate_count':len(candidates)}


def search_tree(a,b,max_length=4,lookahead=2,ratio_bound=16,max_nodes=100,max_rounds=6):
    queue=deque([(a,b,0)])
    seen={(a,b):0}
    records=[]
    while queue and len(records)<max_nodes:
        aa,bb,roundno=queue.popleft()
        params=parameters(aa,bb)
        record={'id':seen[aa,bb],'a':''.join(map(str,aa)),'b':''.join(map(str,bb)),
                'round':roundno,'parameters':[str(p) for p in params]}
        if roundno>=max_rounds:
            result={'status':'round_limit','menu':None}
        else:
            result=discover(aa,bb,max_length,lookahead,ratio_bound)
        record.update(result)
        if result['menu']:
            children=[]
            for u,w in result['menu']:
                child=(aa+tuple(u),bb+tuple(w))
                if child not in seen:
                    seen[child]=len(seen)
                    queue.append((*child,roundno+1))
                children.append(seen[child])
            record['children']=children
        records.append(record)
        print(json.dumps({k:record[k] for k in ('id','a','b','round','status')}),flush=True)
    return {'proof_complete':False,'reason':'No universal closed admissibility table is certified.',
            'settings':{'max_length':max_length,'lookahead':lookahead,'ratio_bound':ratio_bound,
                        'max_nodes':max_nodes,'max_rounds':max_rounds},
            'root':[list(a),list(b)],'records':records,
            'pending':[{'id':seen[aa,bb],'a':list(aa),'b':list(bb),'round':n} for aa,bb,n in queue]}


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--left',default='32113');p.add_argument('--right',default='4322')
    p.add_argument('--length',type=int,default=4);p.add_argument('--lookahead',type=int,default=2)
    p.add_argument('--ratio-bound',type=float,default=16)
    p.add_argument('--nodes',type=int,default=100);p.add_argument('--rounds',type=int,default=6)
    p.add_argument('--output',default='menus_I7.json')
    args=p.parse_args()
    result=search_tree(tuple(map(int,args.left)),tuple(map(int,args.right)),args.length,args.lookahead,
                       args.ratio_bound,args.nodes,args.rounds)
    (DATA/args.output).write_text(json.dumps(result,indent=2)+'\n')
