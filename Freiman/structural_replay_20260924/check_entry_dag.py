#!/usr/bin/env python3
"""Close the structural induction for marked initial entries, separately.

Goodness of the raw H interval is NOT assumed. Geometry/bridge bounds are
separate certificate obligations. Compare every path to the original enumerator.
"""
import ast,itertools,json,hashlib
from collections import Counter
from pathlib import Path
from check_history_dag import children,suffix,need
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'Freiman_Hall_ray_verification/verification/families/target_selection/verify_H_entry_reduction_independent.py'
source=SOURCE.read_bytes();tree=ast.parse(source)
fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='enumerate_all')
env={'product':itertools.product,'need':need}
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(SOURCE),'exec'),env)
roots=[]
for ctx,entry,w in itertools.product(('2','3'),(('1',''),('2','1'),('3','1')),(0,1)):
    s=(suffix(ctx+entry[0]),suffix('313'+entry[1]),*(len(x)%2 for x in entry),w,0)
    roots.append(((ctx,entry,w),s))
graph={};todo=[s for _,s in roots]
while todo:
    s=todo.pop()
    if s in graph:continue
    graph[s]=list(children(s));todo.extend(t for _,t in graph[s])
color={};rank={}
def visit(s):
    need(color.get(s)!=1,'initial-entry cycle')
    if color.get(s)==2:return rank[s]
    color[s]=1;rank[s]=max((1+visit(t) for _,t in graph[s]),default=0);color[s]=2
    return rank[s]
for _,s in roots:visit(s)
paths=set();classified=Counter()
for key,s in roots:
    todo=[(s,())]
    while todo:
        st,path=todo.pop();_,marked,p0,p1,w,_=st
        if marked=='3131':
            paths.add((*key,path))
            classified[('left' if w else 'right') if (p0,p1)==(1,1) else ('mixed' if w else 'rightmixed')]+=1
        for (a,b,reflect),t in graph[st]:todo.append((t,path+(((a,b),reflect),)))
need(paths==set(env['enumerate_all']()),'all 406 initial-entry paths equal')
nodes=sorted(graph);ids={s:i for i,s in enumerate(nodes)}
result=dict(status='PASS_STRUCTURAL_ONLY',states=len(nodes),edges=sum(map(len,graph.values())),
    max_steps_after_entry=max(rank.values()),histories=len(paths),classified=dict(classified),
    source_sha256=hashlib.sha256(source).hexdigest(),
    check='Exact path-set equality to independently enumerated initial histories',
    roots=[dict(context=k[0],entry=k[1],wider=k[2],node=ids[s]) for k,s in roots],
    nodes=[dict(id=ids[s],state=s,rank=rank[s],edges=[dict(label=l,target=ids[t]) for l,t in graph[s]]) for s in nodes])
(HERE/'check_entry_dag.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('nodes','roots')},indent=2))
