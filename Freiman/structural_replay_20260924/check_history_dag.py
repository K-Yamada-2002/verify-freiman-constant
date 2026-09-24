#!/usr/bin/env python3
"""Small structural certificate; NOT an interval-coverage certificate.

Physical side 1 carries the marked suffix. State = other suffix, marked
suffix, physical parities, wider side, previous non-reflected one-sided 1.
Edges overapproximate numeric possibilities using proved forced reflections.
No depth cutoff is used. A cycle causes rejection, rather than truncation.
"""
import json
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q

LABELS = [('1',''),('2',''),('3',''),('','1'),('2','1'),('3','1')]

def need(ok,msg):
    if not ok: raise ArithmeticError(msg)

def suffix(w):
    return next((s for s in ('3131','313','31','3') if w.endswith(s)),w[-1])

def children(state):
    s0,s1,p0,p1,w,previous = state
    words=(s0,s1); par=(p0,p1)
    for a,b in LABELS:
        if not a and p0==p1: continue
        if a=='3' and words[w].endswith('31'): continue
        ext=['',''];ext[w]=a[::-1];ext[1-w]=b
        if ext[1] not in ('','1') or (s1=='3131' and ext[1]): continue
        after=tuple(x+y for x,y in zip(words,ext))
        if any('31313' in x for x in after): continue
        np=tuple((x+len(y))%2 for x,y in zip(par,ext))
        orientations=(w,) if not a else (1-w,) if not b and a in ('2','3') else (0,1)
        if w==0 and not ext[1] and (a,b)==('1','') and previous:
            orientations=(1,)
        for nw in orientations:
            flag=int(w==0 and (a,b)==('1','') and nw==w)
            yield (a,b,nw!=w),(suffix(after[0]),suffix(after[1]),*np,nw,flag)

def certificate():
    roots=[('2','313',1,1,w,0) for w in (0,1)]
    graph={};stack=list(roots)
    while stack:
        s=stack.pop()
        if s in graph:continue
        graph[s]=list(children(s));stack.extend(t for _,t in graph[s])
    color={};rank={}
    def visit(s):
        need(color.get(s)!=1,'cycle in structural suffix histories')
        if color.get(s)==2:return rank[s]
        color[s]=1
        rank[s]=max((1+visit(t) for _,t in graph[s]),default=0)
        color[s]=2
        return rank[s]
    for s in roots:visit(s)
    # Count every distinct path, including merged paths, without expanding words.
    paths=Counter(roots)
    counts=Counter()
    for s in sorted(graph,key=lambda s:rank[s],reverse=True):
        _,mark,p0,p1,w,_=s
        if mark=='3131':
            if (p0,p1)==(0,0):counts['left' if w==1 else 'right']+=paths[s]
            if (p0,p1)==(1,0):counts['mixed' if w==1 else 'rightmixed']+=paths[s]
        for _,t in graph[s]:paths[t]+=paths[s]
    # Six birth contexts remain distinct for geometry, but share this DAG.
    count6={k:6*v for k,v in sorted(counts.items())}
    need(count6==dict(left=594,right=90,mixed=312,rightmixed=90),'source count cross-check')
    need(max(rank.values())<=7,'source length upper-bound cross-check')
    bounds=[Q(187,210),Q(11,14),Q(99,247)*Q(51,35)*Q(61,45)*Q(25,36)]
    need(all(0<x<1 for x in bounds),'forced-reflection rational bounds')
    nodes=sorted(graph);ids={s:i for i,s in enumerate(nodes)}
    return dict(scope='Structural termination only; conditional on numerical goodness and source guarded lists',
        states=len(nodes),edges=sum(map(len,graph.values())),max_steps_after_birth=max(rank.values()),
        histories_per_context=dict(counts),histories_six_contexts=count6,
        rational_reflection_upper_bounds=list(map(str,bounds)),
        roots=[ids[s] for s in roots],
        nodes=[dict(id=ids[s],state=s,rank=rank[s],paths=paths[s],
            edges=[dict(label=lab,target=ids[t]) for lab,t in graph[s]]) for s in nodes])

if __name__=='__main__':
    result=certificate()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='nodes'},indent=2))
