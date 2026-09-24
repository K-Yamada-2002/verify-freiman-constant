#!/usr/bin/env python3
"""Quotient both structural history graphs by simultaneous parity reversal.

Only language/reflection structure is identified. Numerical target order and
source inequalities still need the appropriate parity transformation.
"""
from pathlib import Path
import json
from check_history_dag import children,need
HERE=Path(__file__).resolve().parent

def canonical(s):
    s=list(s)
    if s[3]!=int(s[1]=='313'):s[2]^=1;s[3]^=1
    return tuple(s)

graph={}
for filename in ('check_history_dag.json','check_entry_dag.json'):
    data=json.loads((HERE/filename).read_text());nodes=data['nodes']
    for row in nodes:
        s=tuple(row['state']);c=canonical(s)
        actual={(tuple(e['label']),canonical(nodes[e['target']]['state'])) for e in row['edges']}
        expected={(tuple(label),canonical(t)) for label,t in children(c)}
        need(actual==expected,'parity quotient preserves ALL outgoing labeled edges')
        if c in graph:need(graph[c]==actual,'shared state has identical successors')
        graph[c]=actual
color={};rank={}
def visit(s):
    need(color.get(s)!=1,'joint cycle')
    if color.get(s)==2:return rank[s]
    color[s]=1;rank[s]=max((1+visit(t) for _,t in graph[s]),default=0);color[s]=2
    return rank[s]
for s in graph:visit(s)
nodes=sorted(graph);ids={s:i for i,s in enumerate(nodes)}
result=dict(status='PASS_STRUCTURAL_QUOTIENT',states=len(nodes),edges=sum(map(len,graph.values())),
    max_steps=max(rank.values()),scope='Simultaneous parity quotient of history structure only; not of target inequalities',
    nodes=[dict(id=ids[s],state=s,rank=rank[s],edges=[dict(label=l,target=ids[t]) for l,t in sorted(graph[s])]) for s in nodes])
(HERE/'check_joint_dag.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='nodes'},indent=2))
