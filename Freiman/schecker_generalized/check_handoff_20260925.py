#!/usr/bin/env python3
"""Replay the handoff snapshot. PASS means valid partial work, not closure."""
import argparse,json,time
from pathlib import Path
from collections import deque
from chart_strategy_ranks import report
from reduce_chart_frontier import dependencies
from search_piecewise_charts import restore
from verify_piecewise_charts import PiecewiseVerifier
from repair_root_point_gap import known_gap_hits

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=HERE/'HANDOFF_CHECK_20260925.json')
    args=ap.parse_args();start=time.monotonic()
    graph=json.loads((HERE/'schecker_compact_return_20260924.json').read_text())
    state=json.loads((HERE/'schecker_compact_return_20260924.state.json').read_text())
    checker=PiecewiseVerifier(graph);audit=checker.audit()
    if audit['failed_rules']:raise ValueError('invalid graph')
    search,game,_=restore(state);restored=search.certificate(game)
    restored_checker=PiecewiseVerifier(restored);restored_audit=restored_checker.audit()
    if restored_audit['failed_rules']:raise ValueError('invalid restored graph')
    expected=(3176,1183,1993)
    for g,a in ((graph,audit),(restored,restored_audit)):
        if (len(g['nodes']),len(a['verified_rules']),len(a['open_nodes']))!=expected:
            raise ValueError('unexpected snapshot counts')
    bank=state['gap_filter_bank']
    if len(bank)!=17:raise ValueError('expected 17 saved obstructions')
    hits=known_gap_hits(checker,range(len(graph['nodes'])),bank)
    if hits:raise ValueError('known obstruction hits snapshot')
    closures=[]
    for c in (checker,restored_checker):
        try:verdict=c.closed()
        except ValueError as e:verdict=dict(closed=False,reason=str(e))
        closures.append(verdict)
    deps=dependencies(graph);frontiers={}
    for name,root in graph['roots'].items():
        queue=deque([root]);depth={root:0}
        while queue:
            i=queue.popleft()
            for j in deps[i]:
                if j not in depth:depth[j]=depth[i]+1;queue.append(j)
        first=min(depth[i] for i in audit['open_nodes'] if i in depth)
        frontiers[name]=dict(minimum_depth=first,nodes=[dict(index=i,node=graph['nodes'][i],
                    domain=graph['cells'][graph['nodes'][i]['cell']]) for i in audit['open_nodes'] if depth.get(i)==first])
    result=dict(status='PASS_PARTIAL_HANDOFF_REPLAY',meaning='Partial state verified; Schecker proof remains open',
        graph_hash=checker.proof_hash(),restored_graph_hash=restored_checker.proof_hash(),
        nodes=3176,local_rules=1183,open_nodes=1993,gap_filters=17,known_gap_hits=0,
        ranks=report(graph),closure_results=closures,seconds=time.monotonic()-start,
        fresh_frontiers=frontiers)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='fresh_frontiers'},indent=2))

if __name__=='__main__':main()
