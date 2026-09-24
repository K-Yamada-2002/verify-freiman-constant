#!/usr/bin/env python3
"""Reduce candidate cover to small products of finite cylinder unions.

Each factor has at most three prefixes. This is an actual Cartesian product;
all cross pairs receive an independent rational Perron dominance check.
Numerical interval inclusion remains unproved.
"""
import argparse
from bisect import bisect_right
from collections import defaultdict, deque
from fractions import Fraction as Q
from itertools import combinations
from functools import lru_cache
import json
from pathlib import Path
import time
from target_cover import ThresholdModel,window_library,near_bounds,merge,complement,insert_interval,transform_bounds


def antichain(words):
    out=[]
    for w in sorted(set(words),key=lambda w:(len(w),w)):
        if not any(w.startswith(u) for u in out):out.append(w)
    return tuple(sorted(out))


@lru_cache(None)
def lift(m,word):
    zs=[m.cylinder(word)]
    while zs and len(zs[0][0])<m.radius:
        zs=[c for z in zs for c in m.children(z)]
    return [z[0] for z in zs]


@lru_cache(None)
def atom_dominance(m,u,v):
    return max((near_bounds(a,b,3,m.radius,m.digits,True,m)[1]
                for a in lift(m,u) for b in lift(m,v)),default=Q(0))


def dominance(m,left,right):
    """Exact upper bound for all cross pairs, allowing short prefixes."""
    return max([Q(2)+2*Q(m.digits+1,m.digits+2)]+
               [atom_dominance(m,*sorted((u,v))) for u in left for v in right])


def background(m):
    return max(bound for s,a,t,bound in window_library(m.digits,m.radius)
               if s in m.core and (a,t) in m.edges[s])


def scan_product(m,left,right,target,epsilon,budget,rational=False):
    """Cover with leaves from this ONE product only (all its cross pairs)."""
    stack=[(m.cylinder(u),m.cylinder(v)) for u in left for v in right]
    covered=[];starts=[];qcovered=[];qstarts=[];qwidth=Q(0)
    qtarget=[Q(str(x)) for x in target]
    visited=leaves=0
    while stack and visited<budget:
        x,y=stack.pop();visited+=1
        lo=3+x[3]+y[3];hi=3+x[4]+y[4]
        a=max(target[0],lo);b=min(target[1],hi)
        if a>b:continue
        i=bisect_right(starts,a)-1
        if i>=0 and covered[i][1]>=b:continue
        if x[4]-x[3]+y[4]-y[3]<=epsilon:
            insert_interval(covered,starts,a,b);leaves+=1
            if rational:
                xl,xh=transform_bounds(x[0],m.cert_bounds[x[1]])
                yl,yh=transform_bounds(y[0],m.cert_bounds[y[1]])
                qwidth=max(qwidth,xh-xl+yh-yl)
                qa=max(qtarget[0],3+xl+yl);qb=min(qtarget[1],3+xh+yh)
                if qa<=qb:insert_interval(qcovered,qstarts,qa,qb)
        elif x[4]-x[3]>=y[4]-y[3]:stack.extend((z,y) for z in m.children(x))
        else:stack.extend((x,z) for z in m.children(y))
    return dict(status='budget_exhausted' if stack else 'completed_float',visited=visited,leaves=leaves,
                covered=covered,gaps=complement(covered,*target),
                rational_leaf_check=(dict(covered=[[str(a),str(b)] for a,b in qcovered],maximum_width=str(qwidth)) if rational else None))


def same_language(m,n):
    """Exact equivalence of the two deterministic prefix automata.

    All states have infinite continuations, so finite-prefix language equality
    is equivalent to equality of the corresponding one-sided Cantor sets.
    """
    seen={('','')};todo=deque([('','')])
    while todo:
        s,t=todo.popleft();a=dict(m.edges[s]);b=dict(n.edges[t])
        if set(a)!=set(b):return False,len(seen)
        for digit in a:
            pair=(a[digit],b[digit])
            if pair not in seen:seen.add(pair);todo.append(pair)
    return True,len(seen)


def interval_cover(options,lo=4.1,hi=4.52):
    """Minimum-cardinality cover on each component, classic farthest-end greedy.

    options are (lo,hi,product id). Optimal for these fixed candidate intervals,
    not for all possible Gauss--Cantor definitions.
    """
    options=sorted(options);selected=[];gaps=[];cursor=lo;index=0
    while cursor<hi:
        best=None
        while index<len(options) and options[index][0]<=cursor:
            item=options[index]
            if item[1]>cursor and (best is None or item[1]>best[1]):best=item
            index+=1
        if best is None:
            if index==len(options):gaps.append([cursor,hi]);break
            endpoint=min(hi,options[index][0]);gaps.append([cursor,endpoint]);cursor=endpoint
        else:
            selected.append(best);cursor=best[1]
    return selected,gaps


def build_products(data,maximum_factor=3):
    cache={};models={};groups=defaultdict(list)
    for slab in data['slabs']:
        d=slab['model'];spec=(d['digits'],d['radius'],d['threshold'])
        if spec not in cache:cache[spec]=ThresholdModel(*spec)
        m=cache[spec];sig=m.graph_signature
        if sig not in models:models[sig]=m
        groups[sig].extend(slab['candidates'])
    products=[]
    for gi,(sig,roots) in enumerate(groups.items()):
        m=models[sig];bg=background(m)
        # Shorten each pair when the larger product remains safe everywhere in
        # its previous assigned interval. No new unsafe cross pair is hidden.
        pairs=set()
        for c in roots:
            u,v=c['u'],c['v'];floor=min(Q(str(a)) for a,b in c['intervals'])-Q('0.000002')
            changed=True
            while changed:
                changed=False
                for side in (0,1):
                    a,b=(u[:-1],v) if side==0 else (u,v[:-1])
                    if min(len(a),len(b))<1:continue
                    if max(bg,dominance(m,(a,),(b,)))<floor:
                        u,v=a,b;changed=True;break
            pairs.add(tuple(sorted((u,v))))
        # Every singleton product and every small star are proposed. In a star
        # one side is common, so taking a union introduces no extra cross pairs.
        proposed={( (u,), (v,) ) for u,v in pairs}
        neighbors=defaultdict(set)
        for u,v in pairs:neighbors[u].add(v);neighbors[v].add(u)
        for u,vs in neighbors.items():
            vs=antichain(vs)
            for size in range(2,min(maximum_factor,len(vs))+1):
                for subset in combinations(vs,size):
                    proposed.add(tuple(sorted(((u,),antichain(subset)))))
        # Also try broad rectangles with only short prefix factors (at most 3
        # branches), useful for absorbing intersections of stars. Every such
        # rectangle is checked by dominance(), not assumed from its edges.
        words=antichain(w for pair in pairs for w in pair)
        if len(words)<=6:
            factors=[(w,) for w in words]
            factors += [tuple(v) for n in range(2,min(maximum_factor,len(words))+1) for v in combinations(words,n)]
            for i,A in enumerate(factors):
                for B in factors[i:]:proposed.add((A,B))
        for A,B in sorted(proposed):
            A,B=antichain(A),antichain(B)
            bound=max(bg,dominance(m,A,B))
            low=max(4.1,float(bound)+2e-6)
            if low>=4.52:continue
            products.append(dict(graph=sig,model=m.metadata(),left=A,right=B,dominance_bound=str(bound),target=[low,4.52]))
        print('graph',gi+1,'original roots',len(roots),'short pairs',len(pairs),'products total',len(products),flush=True)
    pruned=[]
    def subset(A,B):
        return all(any(a.startswith(b) for b in B) for a in A)
    for i,c in enumerate(products):
        dominated=False
        for j,d in enumerate(products):
            if i==j or c['graph']!=d['graph'] or d['target'][0]>c['target'][0]:continue
            normal=subset(c['left'],d['left']) and subset(c['right'],d['right'])
            swapped=subset(c['left'],d['right']) and subset(c['right'],d['left'])
            if not(normal or swapped):continue
            reverse=(subset(d['left'],c['left']) and subset(d['right'],c['right'])) or (subset(d['left'],c['right']) and subset(d['right'],c['left']))
            if reverse and d['target'][0]==c['target'][0] and j>i:continue
            dominated=True;break
        if not dominated:pruned.append(c)
    print('exact inclusion pruning',len(products),'->',len(pruned),flush=True)
    return models,pruned


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,default=Path(__file__).with_name('target_complete.json'))
    p.add_argument('--replacement',type=Path,default=Path(__file__).with_name('reduction_449.json'))
    p.add_argument('--epsilon',type=float,default=1e-5)
    p.add_argument('--budget',type=int,default=1000000)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('reduced_search.json'))
    p.add_argument('--max-factor',type=int,default=3)
    args=p.parse_args();start=time.monotonic();data=json.loads(args.input.read_text())
    data['slabs'][39]=json.loads(args.replacement.read_text())['slabs'][0]
    models,products=build_products(data,args.max_factor)
    options=[]
    for i,c in enumerate(products):
        r=scan_product(models[c['graph']],c['left'],c['right'],c['target'],args.epsilon,args.budget)
        c.update(r)
        # A genuine positive overlap is needed to remove roundoff-size seams.
        options.extend((a,b,i) for a,b in r['covered'] if b-a>1e-7)
        if (i+1)%10==0:print('scanned',i+1,'/',len(products),flush=True)
    selected,gaps=interval_cover(options)
    result=dict(status='Numerical candidate propositions, NOT interval inclusion',epsilon=args.epsilon,
                factor_prefix_limit=args.max_factor,products=products,
                selected=[dict(product=i,interval=[a,b]) for a,b,i in selected],
                gaps=gaps,elapsed_seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('selected',len(selected),'gaps',len(gaps),'time',result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
