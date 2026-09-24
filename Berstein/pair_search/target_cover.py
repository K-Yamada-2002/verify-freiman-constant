#!/usr/bin/env python3
"""Target-driven finite-scale cover by safe Gauss--Cantor subshifts.

No interior certificates. Threshold graphs are defined by rational window
upper bounds and restricted to the strongly connected component of 222... .
"""
import argparse
from bisect import bisect_right
from collections import defaultdict, deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json
import hashlib
from pathlib import Path
import time
from search import Model, matrix, merge


@lru_cache(None)
def rational_bounds(word, digits):
    values=[]
    for x in (Q(1,digits+1),Q(digits+1,digits+2)):
        for a in reversed(word): x=1/(int(a)+x)
        values.append(x)
    return min(values),max(values)


@lru_cache(None)
def float_bounds(word,digits):
    a,b,c,d=matrix(word)
    ends=[(a*x+b)/(c*x+d) for x in (1/(digits+1),(digits+1)/(digits+2))]
    return min(ends),max(ends)


@lru_cache(None)
def window_library(digits,radius):
    alphabet=''.join(map(str,range(1,digits+1)))
    out=[]
    for p in product(alphabet,repeat=2*radius+1):
        w=''.join(p)
        # 1,2 centers are uniformly below the whole target range. This shortcut
        # avoids thousands of unnecessary Fraction additions, not any pruning.
        bound=Q(int(w[radius]))+rational_bounds(w[:radius][::-1],digits)[1]+rational_bounds(w[radius+1:],digits)[1]
        out.append((w[:-1],w[-1],w[1:],bound))
    return out


def reachable(graph,start):
    seen={start};stack=[start]
    while stack:
        s=stack.pop()
        for t in graph.get(s,()):
            if t not in seen: seen.add(t);stack.append(t)
    return seen


class ThresholdModel(Model):
    def __init__(self,digits,radius,threshold):
        self.digits,self.radius,self.threshold=digits,radius,Q(threshold)
        self.alphabet=''.join(map(str,range(1,digits+1)))
        self.name=f'D{digits}_r{radius}_H{threshold}'
        self.reset='2'*(2*radius)
        edges=defaultdict(list);forward=defaultdict(list);backward=defaultdict(list)
        for s,a,t,bound in window_library(digits,radius):
            if bound<=self.threshold:
                edges[s].append((a,t));forward[s].append(t);backward[t].append(s)
        core=reachable(forward,self.reset)&reachable(backward,self.reset)
        self.core=core
        self.edges={s:[(a,t) for a,t in edges[s] if t in core] for s in core}
        if any(not es for es in self.edges.values()): raise ValueError('Empty core')
        prefixes={s[:k] for s in core for k in range(2*radius)}
        allstates=core|prefixes
        for s in prefixes:
            self.edges[s]=[(a,s+a) for a in self.alphabet if s+a in allstates]
        self.states=sorted(allstates,key=lambda s:(len(s),s))
        self.graph_signature=hashlib.sha256(' '.join(sorted(s+a for s in core for a,t in self.edges[s])).encode()).hexdigest()
        self.bounds=self.tail_bounds(float,60)
        self.cert_bounds=self.tail_bounds(Q,12)
        # Reverse BFS gives a finite legal route to the all-2 state from every
        # state, including the initial proper-prefix states.
        rev=defaultdict(list)
        for s,es in self.edges.items():
            for a,t in es: rev[t].append((s,a))
        self.connectors={self.reset:''};todo=deque([self.reset])
        while todo:
            t=todo.popleft()
            for s,a in rev[t]:
                if s not in self.connectors:
                    self.connectors[s]=a+self.connectors[t];todo.append(s)
        if len(self.connectors)!=len(self.states): raise ValueError('Missing connector')

    def tail_bounds(self,cast,iterations):
        lo,hi=cast(1)/cast(self.digits+1),cast(self.digits+1)/cast(self.digits+2)
        bounds={s:(lo,hi) for s in self.states}
        for _ in range(iterations):
            bounds={s:(min(1/(cast(a)+bounds[t][1]) for a,t in es),
                       max(1/(cast(a)+bounds[t][0]) for a,t in es)) for s,es in self.edges.items()}
        return bounds

    def metadata(self):
        return dict(digits=self.digits,radius=self.radius,threshold=str(self.threshold),
                    core_states=len(self.core),core_edges=sum(len(self.edges[s]) for s in self.core),
                    reset=self.reset)


def transform_bounds(word,tail):
    a,b,c,d=matrix(word)
    ends=[(a*x+b)/(c*x+d) for x in tail]
    return min(ends),max(ends)


def near_bounds(u,v,center,radius,digits,exact=False,model=None):
    bounds=rational_bounds if exact else float_bounds
    lo=0;hi=0
    for a,b in ((u,v),(v,u)):
        for k in range(min(len(a),radius)):
            if int(a[k])<=2: continue
            if model is None:
                l1,h1=bounds(a[k+1:],digits)
                l2,h2=bounds(a[:k][::-1]+str(center)+b,digits)
            else:
                tails=model.cert_bounds if exact else model.bounds
                l1,h1=transform_bounds(a[k+1:],tails[model.follow(a)])
                l2,h2=transform_bounds(a[:k][::-1]+str(center)+b,tails[model.follow(b)])
            lo=max(lo,int(a[k])+l1+l2);hi=max(hi,int(a[k])+h1+h2)
    return lo,hi


def insert_interval(covered,starts,a,b):
    i=bisect_right(starts,a)
    if i and covered[i-1][1]>=a:
        i-=1;a=min(a,covered[i][0]);b=max(b,covered[i][1])
    j=i
    while j<len(covered) and covered[j][0]<=b:
        b=max(b,covered[j][1]);j+=1
    covered[i:j]=[[a,b]];starts[i:j]=[a]


def complement(intervals,lo,hi):
    gaps=[];cursor=lo
    for a,b in merge(intervals):
        if a>cursor:gaps.append([cursor,min(a,hi)])
        cursor=max(cursor,b)
    if cursor<hi:gaps.append([cursor,hi])
    return [g for g in gaps if g[1]>g[0]]


def scan(model,target,epsilon,budget,prior=(),rational_leaves=False):
    """Retain ALL representations, both central 3 and 4. Never grid-sample.

    Leaf hulls covering already covered regions are skipped only at this scale.
    Every saved root pair passes the near-center bound in rational arithmetic.
    """
    H=float(model.threshold);r=model.radius;D=model.digits
    covered=merge(prior);starts=[a for a,b in covered]
    roots={};pieces=defaultdict(list);visited=leaves=stalled=0
    qcovered=[];qstarts=[];qwidth=Q(0);qtarget=list(map(lambda z:Q(str(z)),target))
    # Symmetry x <-> y is not used here: easy to audit the full branching.
    seeds=[]
    cylinders=model.cylinders('',r)
    for c in (3,4):
        if c>D: continue
        for x in cylinders:
            for y in cylinders:
                a=max(target[0],c+x[3]+y[3]);b=min(target[1],c+x[4]+y[4])
                if a>b: continue
                _,upper=near_bounds(x[0],y[0],c,r,D,model=model)
                seeds.append((upper<=H,b-a,c,x,y))
    seeds.sort(key=lambda z:(z[0],z[1]))
    stack=[(c,x,y,None) for _,_,c,x,y in seeds]
    while stack and visited<budget:
        center,x,y,root=stack.pop();visited+=1
        a=max(target[0],center+x[3]+y[3]);b=min(target[1],center+x[4]+y[4])
        if a>b:continue
        i=bisect_right(starts,a)-1
        if i>=0 and covered[i][1]>=b:continue
        if root is None and (max(len(x[0]),len(y[0]))>=60 or x[4]-x[3]+y[4]-y[3]<1e-14):
            stalled+=1;continue
        if root is None:
            low,high=near_bounds(x[0],y[0],center,r,D,model=model)
            if low>H+1e-12:continue
            if min(len(x[0]),len(y[0]))>=r and high<=H:
                _,upper=near_bounds(x[0],y[0],center,r,D,True,model=model)
                if upper<=model.threshold:
                    root=(center,x[0],y[0]);roots[root]=str(upper)
        if root is not None and x[4]-x[3]+y[4]-y[3]<=epsilon:
            leaves+=1;pieces[root].append((a,b));insert_interval(covered,starts,a,b)
            if rational_leaves:
                xl,xh=transform_bounds(x[0],model.cert_bounds[x[1]])
                yl,yh=transform_bounds(y[0],model.cert_bounds[y[1]])
                qwidth=max(qwidth,xh-xl+yh-yl)
                qa=max(qtarget[0],center+xl+yl);qb=min(qtarget[1],center+xh+yh)
                if qa<=qb:insert_interval(qcovered,qstarts,qa,qb)
        elif x[4]-x[3]>=y[4]-y[3]:
            stack.extend((center,z,y,root) for z in model.children(x))
        else:
            stack.extend((center,x,z,root) for z in model.children(y))
        if len(covered)==1 and covered[0][0]<=target[0] and covered[0][1]>=target[1]:
            break
    gaps=complement(covered,*target)
    return dict(status='covered_float' if not gaps else ('budget_exhausted' if stack else ('precision_unresolved' if stalled else 'gap_float')),
                target=target,epsilon=epsilon,visited=visited,leaves=leaves,stalled=stalled,
                covered=covered,gaps=gaps,
                rational_leaf_check=(dict(covered=[[str(a),str(b)] for a,b in qcovered],
                    maximum_sum_hull_width=str(qwidth),
                    gaps=[[str(a),str(b)] for a,b in complement(qcovered,*qtarget)]) if rational_leaves else None),
                candidates=[dict(center=k[0],u=k[1],v=k[2],near_bound=roots[k],intervals=merge(xs))
                            for k,xs in pieces.items()])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--radius',type=int,default=2)
    p.add_argument('--digits',type=int,default=4,choices=(3,4))
    p.add_argument('--step',default='0.01')
    p.add_argument('--margin',default='0.00001')
    p.add_argument('--epsilon',type=float,default=1e-5)
    p.add_argument('--budget',type=int,default=500000)
    p.add_argument('--rational-leaves',action='store_true')
    p.add_argument('--lo',default='4.1');p.add_argument('--hi',default='4.52')
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('target_cover.json'))
    args=p.parse_args();start=time.monotonic()
    lo,hi,step,margin=map(Q,(args.lo,args.hi,args.step,args.margin))
    if not 1<=args.radius<=4 or not Q('4.1')<=lo<hi<=Q('4.52') or min(step,margin)<=0 or args.epsilon<1e-12 or args.budget<1:
        p.error('Invalid range, radius (1..4), step/margin, epsilon or budget')
    allcovered=[];slabs=[];a=lo
    while a<hi:
        b=min(hi,a+step)
        m=ThresholdModel(args.digits,args.radius,a-margin)
        result=scan(m,[float(a),float(b)],args.epsilon,args.budget,rational_leaves=args.rational_leaves)
        slabs.append(dict(model=m.metadata(),**result));allcovered+=result['covered']
        print(f'{a}..{b}: {result["status"]}, {len(result["gaps"])} gaps, {result["visited"]} nodes, {len(result["candidates"])} roots',flush=True)
        a=b
        data=dict(status='finite-scale numerical cover, NOT interval inclusion',config={k:str(v) if isinstance(v,Path) else v for k,v in vars(args).items()},slabs=slabs,
                  covered=merge(allcovered),gaps=complement(allcovered,float(lo),float(hi)),elapsed_seconds=time.monotonic()-start)
        args.output.write_text(json.dumps(data,indent=2)+'\n')
    print('length',sum(b-a for a,b in data['covered']),'gaps',len(data['gaps']),flush=True)

if __name__=='__main__':main()
