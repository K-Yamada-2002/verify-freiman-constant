#!/usr/bin/env python3
"""Shrink finite unions of scalar intervals on fixed parameter domains.

Only a stationary result replayed by ScalarVerifier is a proof. Grid rounding,
iteration limits, and empty results are search outcomes, not nonexistence proofs.
"""
import argparse
import copy
import hashlib
import json
import time
from pathlib import Path

from close_scalar_library import geometry_moves,common_fragments,merge,close
from repair_gap_intervals import rounded
from verify_scalar_graph import verifier_for


def intersect(left,right):
    return merge((max(a,c),min(b,d)) for a,b in left for c,d in right)


def inward_union(offers,grid):
    # Merge exact overlaps BEFORE rounding. Rounding each offer separately
    # can manufacture a grid-sized gap inside a genuinely connected union.
    return merge((rounded(a,grid,True),rounded(b,grid,False)) for a,b in merge(offers))


def hull(verifier,i):
    a,b=verifier.initial_hull(i)
    return rounded(a,verifier.grid,True),rounded(b,verifier.grid,False)


def search(data,length=2,iterations=20,max_components=2000,return_blocks=False,
           max_seconds=None,progress=None,initial=None,allow_root_shrink=False):
    started=time.monotonic()
    verifier=verifier_for(data)
    moves=geometry_moves(data,length,return_blocks)
    spans=[[hull(verifier,i)] for i in range(len(data['nodes']))]
    for j in data['roots']:
        spans[j]=[tuple(data['nodes'][j]['interval'])]
    history=[]
    if initial is not None:
        if len(initial['intervals'])!=len(spans):
            raise ValueError('checkpoint domain count mismatch')
        resumed=[]
        for i,pieces in enumerate(initial['intervals']):
            for piece in pieces:
                verifier.interval(piece)
            pieces=merge(tuple(piece) for piece in pieces)
            if intersect(spans[i],pieces)!=pieces:
                raise ValueError('checkpoint interval escapes starting hull')
            resumed.append(pieces)
        spans=resumed
        history=list(initial['history'])
    stable=False; reason='iteration limit'
    for iteration in range(len(history),iterations):
        updated=[]
        for i,group in enumerate(moves):
            if max_seconds is not None and time.monotonic()-started>=max_seconds:
                reason='time limit'; break
            if not spans[i]:
                updated.append([]); continue
            offers=[]
            for u,v,cases in group:
                options=[]
                for swap,hbox,dests in cases:
                    rectangles=[(verifier.box(j)[2],span) for j in dests for span in spans[j]]
                    if not rectangles:
                        options.append([]); break
                    outer=(min(span[0] for _,span in rectangles),
                           max(span[1] for _,span in rectangles))
                    bound=verifier.transport(i,u,v,swap,verifier.interval(outer),dests)
                    if not intersect(spans[i],[(bound[0]*verifier.grid,bound[1]*verifier.grid)]):
                        options.append([]); break
                    pieces=common_fragments(hbox,rectangles)
                    cores=[verifier.transport(i,u,v,swap,verifier.interval(piece),dests)
                           for piece in pieces]
                    options.append(merge(cores))
                common=options[0]
                for cores in options[1:]:
                    common=intersect(common,cores)
                offers.extend(common)
            updated.append(intersect(spans[i],inward_union(offers,verifier.grid)))
        if reason=='time limit':
            break
        stable=updated==spans; spans=updated
        row=dict(iteration=iteration+1,domains=sum(bool(s) for s in spans),
                 components=sum(map(len,spans)),
                 root_components=[len(spans[j]) for j in data['roots']],stable=stable)
        history.append(row); print(json.dumps(row),flush=True)
        if progress is not None:
            progress(dict(history=history,intervals=spans,closed=False,reason='running'))
        if stable or not any(spans):
            reason='stationary' if stable else 'empty'; break
        if row['components']>max_components:
            reason='component limit'; break
    report=dict(length=length,return_blocks=return_blocks,geometry_moves=sum(map(len,moves)),
                history=history,reason=reason,intervals=spans,closed=False,
                elapsed_seconds=time.monotonic()-started,
                scope='grid search; no nonexistence inference from an empty result')
    result=None
    if stable and any(spans):
        # Include the unchanged physical root as an additional obligation.
        nodes=[copy.deepcopy(data['nodes'][j]) for j in data['roots']]
        if allow_root_shrink:
            for n,j in zip(nodes,data['roots']):
                if spans[j]:
                    n['interval']=list(max(spans[j],key=lambda span:span[1]-span[0]))
        for i,pieces in enumerate(spans):
            for span in pieces:
                n=copy.deepcopy(data['nodes'][i]); n['interval']=list(span); nodes.append(n)
        for i,n in enumerate(nodes):
            n.update(id=i,covered=False,children=[])
        candidate=dict(data,nodes=nodes,roots=list(range(len(data['roots']))))
        result,verified=close(candidate,length,return_blocks)
        report['stationary_verification']=verified
        report['closed']=verified['closed']
        report['root_shrink_allowed']=allow_root_shrink
    return result,report


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--length',type=int,default=2)
    ap.add_argument('--iterations',type=int,default=20)
    ap.add_argument('--return-blocks',action='store_true')
    ap.add_argument('--max-seconds',type=float)
    ap.add_argument('--max-components',type=int,default=2000)
    ap.add_argument('--resume',type=Path)
    ap.add_argument('--allow-root-shrink',action='store_true')
    args=ap.parse_args(); raw=args.source.read_bytes()
    provenance=dict(source=str(args.source),source_sha256=hashlib.sha256(raw).hexdigest())
    initial=json.loads(args.resume.read_text()) if args.resume else None
    if initial is not None and initial.get('source_sha256')!=provenance['source_sha256']:
        raise ValueError('checkpoint source hash mismatch')
    def checkpoint(report):
        report.update(provenance)
        args.output.with_suffix('.checkpoint.json').write_text(json.dumps(report,indent=2)+'\n')
    result,report=search(json.loads(raw),args.length,args.iterations,return_blocks=args.return_blocks,
                         max_seconds=args.max_seconds,progress=checkpoint,initial=initial,
                         max_components=args.max_components,allow_root_shrink=args.allow_root_shrink)
    report.update(source=str(args.source),source_sha256=hashlib.sha256(raw).hexdigest())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    if result is not None:
        args.output.with_suffix('.graph.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
