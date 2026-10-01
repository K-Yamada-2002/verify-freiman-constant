"""Search long mixed successors only where the current cover is incomplete.

Numeric screening is for discovery. Every successful reported local menu is
checked with exact endpoints. A rejected node is still refined, so its good
descendants can replace it. This is not yet an infinite admissibility proof.
"""
import argparse
import heapq
import json
import time
from pathlib import Path
from layout import DATA
from exact_cf import interval,parameters,union
from menu_search import branch,extensions,geometric_holes,merge_float
from obstruction_probe import scan,step,DIGITS


def extend(data,digit):
    word,state,(a,b,c,d)=data
    state=step(state,digit)
    return None if state is None else (word+(digit,),state,(b,a+digit*b,d,c+digit*d))


def exact_menu(a,b,candidates):
    # Exact greedy replay; endpoints of the parent must be reached exactly.
    ivs=sorted((interval(a+u,b+w),u,w) for _,_,u,w in candidates)
    pl,pu=interval(a,b);end=pl;chosen=[]
    while end<pu:
        possibilities=[row for row in ivs if row[0][0]<=end<row[0][1]]
        if not possibilities:return None
        best=max(possibilities,key=lambda row:row[0][1])
        chosen.append((best[1],best[2]));end=best[0][1]
    assert union([interval(a+u,b+w) for u,w in chosen])==[(pl,pu)]
    return chosen


def search(a,b,max_length=24,lookahead=4,ratio_bound=100,max_nodes=100000,
           banned=frozenset(),progress=False):
    r,s,rho=map(float,parameters(a,b));pa,pb=len(a)%2,len(b)%2
    ea=extensions(scan(a),0)[0];eb=extensions(scan(b),0)[0]
    parent_a=branch(r,pa,ea)[0];parent_b=branch(s,pb,eb)[0]
    pl=parent_a[0]+rho*parent_b[0];pu=parent_a[1]+rho*parent_b[1]
    queue=[(0,0,ea,eb)];seen={((),())};serial=1;accepted=[];cover=[]
    leaves=[];splits=[]
    counts={'processed':0,'tested':0,'intrinsic_screen_rejections':0,'banned_rejections':0,
            'covered_prunes':0,'length_limit':0,'max_length_seen':0}
    start=time.monotonic()
    def push(x,y):
        nonlocal serial
        key=x[0],y[0]
        if key in seen:return
        seen.add(key);length=len(x[0])+len(y[0])
        heapq.heappush(queue,(length,serial,x,y));serial+=1
    while queue and counts['processed']<max_nodes:
        total,_,aa,bb=heapq.heappop(queue);u,w=aa[0],bb[0]
        counts['processed']+=1;counts['max_length_seen']=max(counts['max_length_seen'],total)
        ia,rr,qa=branch(r,pa,aa);ib,ss,qb=branch(s,pb,bb)
        lo,hi=ia[0]+rho*ib[0],ia[1]+rho*ib[1]
        if any(cl<=lo+1e-14 and hi<=ch+1e-14 for cl,ch in cover):
            counts['covered_prunes']+=1;leaves.append((u,w));continue
        rhoc=rho*(qa/qb)**2
        balanced=1/ratio_bound<=rhoc<=ratio_bound
        forbidden=(a+u,b+w) in banned
        if total and balanced and not forbidden:
            counts['tested']+=1
            holes=geometric_holes(aa[1],bb[1],(pa+len(u))%2,(pb+len(w))%2,rr,ss,rhoc,lookahead)
            if not holes:
                accepted.append((lo,hi,u,w));cover=merge_float((x,y) for x,y,_,_ in accepted)
                leaves.append((u,w))
                if len(cover)==1 and cover[0][0]<=pl+1e-13 and cover[0][1]>=pu-1e-13:
                    menu=exact_menu(a,b,accepted)
                    if menu is not None:
                        return {'status':'exact_local_cover','menu':[[list(u),list(w)] for u,w in menu],
                                'counts':counts,'seconds':time.monotonic()-start,
                                'accepted_count':len(accepted),'pending':len(queue)}
                continue
            counts['intrinsic_screen_rejections']+=1
        elif forbidden:counts['banned_rejections']+=1
        if total>=max_length:
            counts['length_limit']+=1;leaves.append((u,w));continue
        split_sides=[]
        if rhoc<=ratio_bound:
            split_sides.append('left')
            for d in DIGITS:
                child=extend(aa,d)
                if child is not None:push(child,bb)
        if rhoc>=1/ratio_bound:
            split_sides.append('right')
            for d in DIGITS:
                child=extend(bb,d)
                if child is not None:push(aa,child)
        splits.append((u,w,split_sides))
        if progress and counts['processed']%5000==0:
            print(json.dumps({'progress':counts,'pending':len(queue),'seconds':time.monotonic()-start}),flush=True)
    gaps=[];end=pl
    for lo,hi in cover:
        if lo>end+1e-13:gaps.append([end,lo])
        end=max(end,hi)
    if end<pu-1e-13:gaps.append([end,pu])
    leaves.extend((aa[0],bb[0]) for _,_,aa,bb in queue)
    outer=union([interval(a+u,b+w) for u,w in leaves])
    intrinsic=[(x[1],y[0]) for x,y in zip(outer,outer[1:])]
    return {'status':'certified_intrinsic_gap' if intrinsic else 'unresolved',
            'menu':None,'counts':counts,'pending':len(queue),
            'accepted_count':len(accepted),'normalized_uncovered':gaps,
            'intrinsic_gaps':[[v.data() for v in gap] for gap in intrinsic],
            'intrinsic_gaps_decimal':[[float(v) for v in gap] for gap in intrinsic],
            'outer_certificate':{'leaves':[[list(u),list(w)] for u,w in leaves],
                                 'splits':[[list(u),list(w),sides] for u,w,sides in splits]},
            'seconds':time.monotonic()-start}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--left',default='321133');p.add_argument('--right',default='432212')
    p.add_argument('--length',type=int,default=24);p.add_argument('--lookahead',type=int,default=4)
    p.add_argument('--nodes',type=int,default=100000)
    p.add_argument('--output',default='adaptive_menu.json');args=p.parse_args()
    result={'proof_complete':False,'settings':vars(args),
            **search(tuple(map(int,args.left)),tuple(map(int,args.right)),args.length,args.lookahead,
                     max_nodes=args.nodes,progress=True)}
    (DATA/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
