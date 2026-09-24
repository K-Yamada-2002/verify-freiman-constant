#!/usr/bin/env python3
"""Recombine saved proper-digit covers without introducing new types."""
import argparse
import json
from pathlib import Path
import time
from hybrid_discovery import Mosaic
from search_complete_induction import atomic_json
from chart_strategy_ranks import report
from verify_piecewise_charts import PiecewiseVerifier


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path);ap.add_argument('--resume',type=Path)
    ap.add_argument('--seconds',type=float,default=180)
    ap.add_argument('--first',type=int,nargs='*',default=[])
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if args.seconds<=0:ap.error('positive time budget required')
    source=json.loads(args.graph.read_text());source_hash=PiecewiseVerifier(source).proof_hash()
    if args.resume:
        saved=json.loads(args.resume.read_text())
        if saved['source_proof_hash']!=source_hash:raise ValueError('resume source identity mismatch')
        lane=Mosaic(state=saved['mosaic'])
    else:
        lane=Mosaic(source)
        if any(i not in lane.targets for i in args.first):raise ValueError('priority target must be open')
        lane.targets=list(dict.fromkeys(args.first+lane.targets))
    initial_nodes=len(lane.graph['nodes']);start=time.monotonic();last=start
    def save():
        atomic_json(args.output,lane.graph)
        atomic_json(args.output.with_suffix('.mosaic.state.json'),dict(source_proof_hash=source_hash,mosaic=lane.snapshot()))
        summary=dict(source_proof_hash=source_hash,statistics=lane.statistics,completed_targets=lane.position,
                     total_targets=len(lane.targets),finished=lane.finished,seconds=time.monotonic()-start,
                     ranks=report(lane.graph),scope='Saved-cover recombination only; no new induction types')
        atomic_json(args.output.with_suffix('.report.json'),summary)
        print(json.dumps(summary),flush=True)
    while not lane.finished and time.monotonic()-start<args.seconds:
        lane.step()
        if time.monotonic()-last>=30:save();last=time.monotonic()
    if len(lane.graph['nodes'])!=initial_nodes:raise ValueError('new node introduced')
    checker=PiecewiseVerifier(lane.graph);audit=checker.audit()
    if audit['failed_rules']:raise ValueError('recombined local rule failed independent audit')
    atomic_json(args.output.with_suffix('.audit.json'),audit)
    try:closure=checker.closed()
    except ValueError as error:closure=dict(closed=False,reason=str(error))
    atomic_json(args.output.with_suffix('.closure.json'),closure);save()

if __name__=='__main__':main()
