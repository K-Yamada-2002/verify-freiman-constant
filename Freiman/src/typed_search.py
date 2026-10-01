"""Adaptive local menus for F and resettable T2 auxiliary intervals."""
import argparse
import heapq
import json
import time
from pathlib import Path
from layout import DATA
from functools import lru_cache
import numpy as np
from exact_cf import parameters
from menu_search import branch,extensions,cylinder_array,merge_float
from obstruction_probe import scan,DIGITS
from adaptive_menus import extend
from typed_intervals import hull,normalized_interval,merged


def screening_components(sa,sb,pa,pb,r,s,rho,depth):
    xa=cylinder_array(sa,depth);xb=cylinder_array(sb,depth)
    aa=xa/(1+r*xa);bb=xb/(1+s*xb)
    if pa:aa=-aa[:,::-1]
    if pb:bb=-bb[:,::-1]
    lo=(aa[:,None,0]+rho*bb[None,:,0]).ravel()
    hi=(aa[:,None,1]+rho*bb[None,:,1]).ravel()
    order=np.argsort(lo);lo=lo[order];hi=np.maximum.accumulate(hi[order])
    breaks=np.flatnonzero(lo[1:]>hi[:-1]+1e-13)
    starts=np.r_[0,breaks+1];ends=np.r_[breaks,len(lo)-1]
    return tuple(zip(lo[starts],hi[ends]))


def point_menu(a,b,kind,candidates):
    ivs=[(hull(a+u,b+w,t),u,w,t) for _,_,u,w,t in candidates]
    pl,pu=hull(a,b,kind);end=pl;chosen=[]
    while end<pu:
        possibilities=[x for x in ivs if x[0][0]<=end<x[0][1]]
        if not possibilities:return None
        best=max(possibilities,key=lambda x:(min(x[0][1],pu),x[3]=='T2',-(len(x[1])+len(x[2]))))
        chosen.append((best[1],best[2],best[3]));end=best[0][1]
    components=merged([hull(a+u,b+w,t) for u,w,t in chosen])
    assert any(lo<=pl and pu<=hi for lo,hi in components)
    return chosen


def search(a,b,kind='F',max_length=20,lookahead=4,ratio_bound=100,
           max_nodes=20000,banned=frozenset(),allowed_types=('T2','F'),
           params=None,candidate_guard=None,menu_selector=None):
    if params is not None and menu_selector is None:
        raise ValueError('Abstract parameters require an explicit exact menu selector')
    r,s,rho=map(float,parameters(a,b) if params is None else params);pa,pb=len(a)%2,len(b)%2
    ea=extensions(scan(a),0)[0];eb=extensions(scan(b),0)[0]
    pl,pu=normalized_interval(r,s,rho,pa,pb,ea,eb,kind)
    queue=[(0,0,ea,eb)];serial=1;seen={((),())};accepted=[];cover=[]
    counts={'processed':0,'screened':0,**{'accepted_'+t:0 for t in allowed_types},'max_length_seen':0,
            'banned_rejections':0,'length_limit':0}
    start=time.monotonic()
    def push(x,y):
        nonlocal serial
        key=x[0],y[0]
        if key in seen:return
        seen.add(key);heapq.heappush(queue,(len(x[0])+len(y[0]),serial,x,y));serial+=1
    while queue and counts['processed']<max_nodes:
        total,_,aa,bb=heapq.heappop(queue);u,w=aa[0],bb[0]
        counts['processed']+=1;counts['max_length_seen']=max(counts['max_length_seen'],total)
        ia,rr,qa=branch(r,pa,aa);ib,ss,qb=branch(s,pb,bb)
        lo,hi=ia[0]+rho*ib[0],ia[1]+rho*ib[1]
        if hi<pl-1e-14 or lo>pu+1e-14:continue
        # Point coverage is not a certificate of coverage throughout a box.
        # Keep alternative rectangles after a uniform selector has rejected a
        # midpoint cover; otherwise its next candidates were all pruned away.
        if menu_selector is None and any(cl<=max(lo,pl)+1e-14 and min(hi,pu)<=ch+1e-14 for cl,ch in cover):continue
        rhoc=rho*(qa/qb)**2;accepted_full=False
        if total and 1/ratio_bound<=rhoc<=ratio_bound:
            components=screening_components(aa[1],bb[1],(pa+len(u))%2,(pb+len(w))%2,rr,ss,rhoc,lookahead)
            counts['screened']+=1
            ca=extensions(aa[1],0)[0];cb=extensions(bb[1],0)[0]
            for typ in allowed_types:
                if (a+u,b+w,typ) in banned:
                    counts['banned_rejections']+=1;continue
                if candidate_guard is not None and not candidate_guard(u,w,typ):
                    counts['banned_rejections']+=1;continue
                cl,ch=normalized_interval(rr,ss,rhoc,(pa+len(u))%2,(pb+len(w))%2,ca,cb,typ)
                if not any(ll<=cl+1e-13 and ch<=hh+1e-13 for ll,hh in components):continue
                tl,th=normalized_interval(r,s,rho,pa,pb,aa,bb,typ)
                if th<pl or tl>pu:continue
                accepted.append((tl,th,u,w,typ));counts['accepted_'+typ]+=1
                if typ=='F':accepted_full=True
            if accepted:
                cover=merge_float((x,y) for x,y,*_ in accepted)
                if any(lo<=pl+1e-13 and pu<=hi+1e-13 for lo,hi in cover):
                    menu=(point_menu(a,b,kind,accepted) if menu_selector is None
                          else menu_selector(accepted))
                    if menu is not None:
                        return {'status':'exact_local_cover','menu':[[list(u),list(w),t] for u,w,t in menu],
                                'counts':counts,'seconds':time.monotonic()-start}
        if accepted_full:continue
        if total>=max_length:counts['length_limit']+=1;continue
        if rhoc<=ratio_bound:
            for d in DIGITS:
                child=extend(aa,d)
                if child is not None:push(child,bb)
        if rhoc>=1/ratio_bound:
            for d in DIGITS:
                child=extend(bb,d)
                if child is not None:push(aa,child)
    gaps=[];end=pl
    for lo,hi in cover:
        if lo>end+1e-13:gaps.append([end,lo])
        end=max(end,hi)
    if end<pu-1e-13:gaps.append([end,pu])
    return {'status':'unresolved','menu':None,'counts':counts,'pending':len(queue),
            'normalized_uncovered':gaps,'seconds':time.monotonic()-start}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--left',default='32113');p.add_argument('--right',default='4322')
    p.add_argument('--type',choices=['F','T2'],default='F');p.add_argument('--length',type=int,default=20)
    p.add_argument('--lookahead',type=int,default=4);p.add_argument('--nodes',type=int,default=20000)
    p.add_argument('--output',default='typed_menu.json');args=p.parse_args()
    result={'proof_complete':False,'settings':vars(args),**search(tuple(map(int,args.left)),tuple(map(int,args.right)),
            args.type,args.length,args.lookahead,max_nodes=args.nodes)}
    (DATA/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
