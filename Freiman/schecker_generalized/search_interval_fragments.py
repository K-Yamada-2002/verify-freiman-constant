#!/usr/bin/env python3
"""Compile split discovery targets to ordinary proper-digit Schecker rules.

No new induction axiom or verifier schema: the unchanged PiecewiseVerifier
checks every accepted rule and both original full-hull root families.
"""
import argparse
import copy
import hashlib
from itertools import product
import json
from pathlib import Path
import time
from chart_geometry import Domain, compare
from finite_type_game import Game
from hybrid_discovery import Constructive
from repair_root_point_gap import install_bank
from search_piecewise_charts import PiecewiseSearch, fingerprint
from search_root_frontier import prioritize
from chart_strategy_ranks import report
from type_graph_geometry import Cell, endpoint, exchange
from learn_small_type_menu import template_labels
from verify_piecewise_charts import PiecewiseVerifier


def intersect_domains(a,b):
    if (a.words,a.high,a.base.states,a.base.parity,a.base.high)!=(b.words,b.high,b.base.states,b.base.parity,b.base.high):
        raise ValueError('fragment guards must use a common parameter chart')
    boxes=[]
    for x,y in zip((a.base.r,a.base.s,a.base.ratio),(b.base.r,b.base.s,b.base.ratio)):
        lo,hi=max(x[0],y[0]),min(x[1],y[1])
        if hi<lo:return None
        boxes.append((lo,hi))
    return Domain(Cell(a.base.states,a.base.parity,a.base.high,*boxes),a.words,a.high)


def compile_fragments(search,key,proposals):
    """Intersect guard partitions; concatenate offers; independently replay."""
    cid,lo,hi=key;pieces=[dict(cell=cid,children=[])]
    for plan,_ in proposals:
        other=plan['pieces'] if isinstance(plan,dict) else [dict(cell=cid,children=plan)]
        merged=[]
        for a,b in product(pieces,other):
            part=intersect_domains(search.cells[a['cell']],search.cells[b['cell']])
            if part is not None:
                merged.append(dict(cell=search.register(part),children=a['children']+b['children']))
        pieces=merged
    final=[];deps=[];low=search.points(cid)[lo][2]
    for piece in pieces:
        domain=search.cells[piece['cell']];current=low;edges=[]
        for edge in piece['children']:
            upper=endpoint(domain.states,edge['upper'],edge['suffixes'])
            if compare(domain,current,upper):continue
            edges.append(copy.deepcopy(edge));current=upper
        final.append(dict(cell=piece['cell'],children=edges))
        deps.extend(d['key'] for e in edges for d in e['destinations'])
    deps=list(dict.fromkeys(deps))
    plan=final[0]['children'] if len(final)==1 and final[0]['cell']==cid else dict(pieces=final)
    probe=Game([key])
    for child in deps:probe.add(child)
    probe.entries[0].update(status='local',plan=plan,children=[probe.ids[k] for k in deps])
    PiecewiseVerifier(search.certificate(probe)).local(0)
    return plan,deps


class FragmentSearch(PiecewiseSearch):
    def configure_fragments(self,depth=1,cuts=3):
        self.fragment_depth=depth;self.fragment_cuts=cuts
        self.fragment_statistics=dict(parent_attempts=0,part_attempts=0,accepted=0,compile_rejected=0)
        self.fragment_rows=[]

    def ensure_target_shape(self,key):
        cid,lo,hi=key;points=self.points(cid)
        try:template_labels(self.cells[cid].states,points[lo][2],points[hi][2],self.shape_menu)
        except ValueError:
            shape=tuple(tuple(points[i][1]) for i in (lo,hi))
            self.shape_menu=tuple(dict.fromkeys(self.shape_menu+(shape,tuple(exchange(z) for z in shape))))
            self.shape_pairs.cache_clear();self.native_geometry.cache_clear()

    def planner(self,key,rejected):
        proposal=super().planner(key,rejected)
        if proposal is not None:return proposal
        if key in self.game.permanent_rejections:return None
        self.fragment_statistics['parent_attempts']+=1;memo={}
        def solve(k,depth,already_failed=False):
            cache=k,depth
            if cache in memo:return memo[cache]
            if not already_failed:
                self.fragment_statistics['part_attempts']+=1
                self.ensure_target_shape(k)
                result=super(FragmentSearch,self).planner(k,rejected)
                if result is not None:
                    memo[cache]=result;return result
            if depth<=0 or k in self.game.permanent_rejections:
                memo[cache]=None;return None
            cid,lo,hi=k;points=self.points(cid);domain=self.cells[cid]
            lower,upper=points[lo][2],points[hi][2]
            middle=(self.value(cid,points[lo][0])+self.value(cid,points[hi][0]))/2
            candidates=sorted((i for i in range(len(points)) if i not in (lo,hi)),
                              key=lambda i:abs(self.value(cid,points[i][0])-middle))
            tried=0
            for cut in candidates:
                if not (compare(domain,points[cut][2],lower,strict=True) and compare(domain,upper,points[cut][2],strict=True)):continue
                tried+=1;left=solve((cid,lo,cut),depth-1)
                right=solve((cid,cut,hi),depth-1) if left is not None else None
                if left is not None and right is not None:
                    try:result=compile_fragments(self,k,[left,right])
                    except ValueError:self.fragment_statistics['compile_rejected']+=1
                    else:
                        self.fragment_rows.append(dict(key=k,cut=points[cut][1],depth=depth))
                        memo[cache]=result;return result
                if tried>=self.fragment_cuts:break
            memo[cache]=None;return None
        result=solve(key,self.fragment_depth,already_failed=True)
        if result is not None:self.fragment_statistics['accepted']+=1
        return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state',type=Path);ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--attempts',type=int,default=8)
    ap.add_argument('--depth',type=int,default=1);ap.add_argument('--cuts',type=int,default=3)
    ap.add_argument('--focus-root',choices=('zero','positive'),default='zero')
    ap.add_argument('--native-executable',type=Path)
    ap.add_argument('--planner-seconds',type=float,default=30)
    ap.add_argument('--balance',type=str)
    ap.add_argument('--max-step',type=int)
    ap.add_argument('--chart-memory',type=int)
    args=ap.parse_args()
    if min(args.seconds,args.attempts,args.depth,args.cuts,args.planner_seconds)<=0:ap.error('positive limits required')
    saved=json.loads(args.state.read_text())
    for name in ('balance','max_step','chart_memory'):
        val=getattr(args,name)
        if val is not None:saved['configuration'][name]=val
    lane=Constructive(saved)
    lane.search.__class__=FragmentSearch;lane.search.configure_fragments(args.depth,args.cuts)
    if args.native_executable:lane.search.native_executable=args.native_executable.resolve()
    bank=saved.get('gap_filter_bank',[]);install_bank(lane.search,bank)
    from planner_time_limit import bounded_planner
    lane.search.planner=bounded_planner(lane.search,args.planner_seconds)
    start=time.monotonic();rows=[]
    def save():
        graph=lane.graph();state=lane.search.snapshot(lane.game,lane.config,fingerprint());state['gap_filter_bank']=bank
        state['fragment_discovery']=dict(engine_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            source_state_sha256=hashlib.sha256(args.state.read_bytes()).hexdigest(),depth=args.depth,cuts=args.cuts)
        summary=dict(status='partial Schecker induction; no Freiman filling lemma assumed',attempts=rows,
                     fragments=lane.search.fragment_statistics,fragment_cuts=lane.search.fragment_rows,
                     planner_timeouts=getattr(lane.search,'planner_timeouts',0),
                     ranks=report(graph),seconds=time.monotonic()-start)
        for path,data in ((args.output,graph),(args.output.with_suffix('.state.json'),state),(args.output.with_suffix('.report.json'),summary)):
            temporary=path.with_suffix('.tmp');temporary.write_text(json.dumps(data,separators=(',',':'))+'\n');temporary.replace(path)
        return graph
    save()
    try:
        while len(rows)<args.attempts and time.monotonic()-start<args.seconds and lane.todo:
            depth=prioritize(lane,[lane.game.roots[('zero','positive').index(args.focus_root)]])
            i=lane.todo[0]
            if i not in depth:break
            before=lane.statistics['accepted'];t=time.monotonic();lane.step()
            row=dict(node=i,root_depth=depth[i],accepted=lane.statistics['accepted']>before,elapsed=time.monotonic()-t,
                     unresolved=lane.game.summary()['unresolved'])
            rows.append(row);save();print(json.dumps(row),flush=True)
    finally:lane.search.close_native()
    graph=save();checker=PiecewiseVerifier(graph);audit=checker.audit()
    if audit['failed_rules']:raise ValueError('fragment output failed independent audit')
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    try:verdict=checker.closed()
    except ValueError as error:verdict=dict(closed=False,reason=str(error))
    args.output.with_suffix('.closure.json').write_text(json.dumps(verdict,indent=2)+'\n')
    print(json.dumps(dict(ranks=report(graph),verification=verdict)),flush=True)

if __name__=='__main__':main()
