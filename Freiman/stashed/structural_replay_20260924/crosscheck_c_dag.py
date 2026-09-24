#!/usr/bin/env python3
"""Compile C89 implementation and compare every node/rank/edge with Python."""
import json, re, subprocess, tempfile
from pathlib import Path
from check_history_dag import certificate, LABELS, need

HERE=Path(__file__).resolve().parent
SUFFIXES=('1','2','3','31','313','3131')
def packed(s):
    s0,s1,p0,p1,w,flag=s
    return SUFFIXES.index(s0)|((s1=='3131')<<3)|(p0<<4)|(p1<<5)|(w<<6)|(flag<<7)
with tempfile.TemporaryDirectory(prefix='freiman-c89-') as tmp:
    exe=str(Path(tmp)/'checker')
    subprocess.run(['cc','-std=c89','-Wall','-Wextra','-Werror','-pedantic','-O2',str(HERE/'history_dag.c'),'-o',exe],check=True)
    out=subprocess.check_output([exe],text=True)
data=certificate(); nodes=data['nodes']; actual_nodes={}; actual_edges=set()
for line in out.splitlines():
    if line.startswith('NODE '):
        s,r=map(int,line.split()[1:]);need(s not in actual_nodes,'duplicate node');actual_nodes[s]=r
    if line.startswith('EDGE '):
        edge=tuple(map(int,line.split()[1:]));need(edge not in actual_edges,'duplicate edge');actual_edges.add(edge)
expected_nodes={packed(n['state']):n['rank'] for n in nodes}
expected_edges=set()
for n in nodes:
    for e in n['edges']:
        a,b,reflect=e['label']; t=nodes[e['target']]
        expected_edges.add((packed(n['state']),LABELS.index((a,b)),t['state'][4],packed(t['state'])))
need(actual_nodes==expected_nodes,'all states and ranks')
need(actual_edges==expected_edges,'all labeled transitions')
entry=json.loads((HERE/'check_entry_dag.json').read_text())
enodes=entry['nodes']
anodes={}; aedges=set()
for line in out.splitlines():
    if line.startswith('ENTRY_NODE '):
        state,rank=map(int,line.split()[1:]);need(state not in anodes,'duplicate entry node');anodes[state]=rank
    if line.startswith('ENTRY_EDGE '):
        edge=tuple(map(int,line.split()[1:]));need(edge not in aedges,'duplicate entry edge');aedges.add(edge)
en={packed(n['state']):n['rank'] for n in enodes};ee=set()
for n in enodes:
    for e in n['edges']:
        a,b,reflect=e['label'];t=enodes[e['target']]
        ee.add((packed(n['state']),LABELS.index((a,b)),t['state'][4],packed(t['state'])))
need(anodes==en and aedges==ee,'all initial-entry states, ranks and edges')
(HERE/'history_c_replay.txt').write_text(out)
result=dict(status='PASS',check='Exact labeled graph and rank equality, C89 vs Python',
            states=len(actual_nodes),edges=len(actual_edges),initial_states=len(anodes),initial_edges=len(aedges),static_storage_bytes=int(re.search(r'Static tables and counters: (\d+) bytes',out).group(1)),
            scope='structural history only; excludes numeric coverage and runtime/stack memory')
(HERE/'history_c_crosscheck.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
