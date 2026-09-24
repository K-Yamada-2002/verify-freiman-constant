#!/usr/bin/env python3
"""Prioritize the shortest unproved root branches, retaining every obligation.

Finite expansion depth is the progress measure used in the Berstein audit.
This conservative lane never deletes an existing parent after a failed probe.
It saves a normal piecewise search state and exact-audited partial graph.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import time

from chart_strategy_ranks import report
from hybrid_discovery import Constructive
from search_piecewise_charts import fingerprint
from verify_piecewise_charts import PiecewiseVerifier
from repair_root_point_gap import install_bank


def prioritize(lane, roots=None):
    depth={i:0 for i in (lane.game.roots if roots is None else roots)};queue=deque(depth)
    while queue:
        i=queue.popleft()
        if lane.game.entries[i]['status']!='local':
            continue
        for j in lane.game.entries[i]['children']:
            if j not in depth:
                depth[j]=depth[i]+1;queue.append(j)
    lane.todo=deque(sorted(lane.todo,key=lambda i:(depth.get(i,float('inf')),
                            -len(lane.game.entries[i]['parents']),i)))
    return depth


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state',type=Path)
    ap.add_argument('--seconds',type=float,default=300)
    ap.add_argument('--attempts',type=int,default=40)
    ap.add_argument('--max-step',type=int,default=2)
    ap.add_argument('--max-shapes',type=int)
    ap.add_argument('--partition-depth',type=int)
    ap.add_argument('--chart-memory',type=int)
    ap.add_argument('--native-executable',type=Path)
    ap.add_argument('--focus-root',choices=('zero','positive'))
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if min(args.seconds,args.attempts,args.max_step)<=0:ap.error('positive budgets required')
    saved=json.loads(args.state.read_text())
    lane=Constructive(saved)
    lane.search.max_step=args.max_step;lane.config['max_step']=args.max_step
    if args.max_shapes is not None:
        if args.max_shapes<2:ap.error('at least two endpoint shapes required')
        lane.search.max_shapes=args.max_shapes;lane.config['max_shapes']=args.max_shapes
    if args.partition_depth is not None:
        if args.partition_depth<0:ap.error('nonnegative partition depth required')
        lane.search.partition_depth=args.partition_depth
        lane.config['partition_depth']=args.partition_depth
    if args.chart_memory is not None:
        if args.chart_memory<1:ap.error('positive chart memory required')
        lane.search.chart_memory=args.chart_memory;lane.config['chart_memory']=args.chart_memory
    lane.search.moves.cache_clear();lane.search.native_geometry.cache_clear()
    if args.native_executable:lane.search.native_executable=args.native_executable.resolve()
    bank=saved.get('gap_filter_bank',[])
    install_bank(lane.search,bank)
    rows=[];start=time.monotonic()
    roots=None if args.focus_root is None else [lane.game.roots[('zero','positive').index(args.focus_root)]]
    def save():
        graph=lane.graph()
        state=lane.search.snapshot(lane.game,lane.config,fingerprint())
        state['gap_filter_bank']=bank
        summary=dict(status='partial induction; no closure claim',attempts=rows,
                     statistics=lane.statistics,ranks=report(graph),seconds=time.monotonic()-start,
                     focus_root=args.focus_root,gap_filters=len(bank))
        for path,data in ((args.output,graph),(args.output.with_suffix('.state.json'),state),
                          (args.output.with_suffix('.report.json'),summary)):
            temp=path.with_suffix('.tmp');temp.write_text(json.dumps(data,separators=(',',':'))+'\n');temp.replace(path)
        return graph
    save()
    try:
        while len(rows)<args.attempts and time.monotonic()-start<args.seconds and lane.todo:
            depth=prioritize(lane,roots);i=lane.todo[0]
            if i not in depth:break
            before=dict(lane.statistics);t=time.monotonic()
            lane.step()
            row=dict(node=i,root_depth=depth.get(i),accepted=lane.statistics['accepted']>before['accepted'],
                     elapsed=time.monotonic()-t,unresolved=lane.game.summary()['unresolved'])
            rows.append(row);save();print(json.dumps(row),flush=True)
            if lane.game.closed():break
    finally:lane.search.close_native()
    graph=save();checker=PiecewiseVerifier(graph);audit=checker.audit()
    if audit['failed_rules']:raise ValueError('frontier output failed exact audit')
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    try:verdict=checker.closed()
    except ValueError as error:verdict=dict(closed=False,reason=str(error))
    else:args.output.with_suffix('.verified.json').write_text(json.dumps(verdict,indent=2)+'\n')
    print(json.dumps(dict(ranks=report(graph),verification=verdict)),flush=True)


if __name__=='__main__':main()
