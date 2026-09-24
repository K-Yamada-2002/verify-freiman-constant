#!/usr/bin/env python3
"""Floating discovery on an exactly compiled parameter-return graph.

Empty numerical iterates do not prove nonexistence. Every successful fixed
point is sent back to the exact kernel and full physical-seed verifier.
"""
import argparse
import hashlib
import json
import math
import time
from pathlib import Path

from anchored_geometry import B
from exact import F
from close_scalar_library import geometry_moves,merge
from scalar_geometry import quadratic_parameters
from search_return_kernel import search
from verify_scalar_graph import verifier_for


def intersect(a,b):
    out=[]; i=j=0
    while i<len(a) and j<len(b):
        lo,hi=max(a[i][0],b[j][0]),min(a[i][1],b[j][1])
        if lo<hi: out.append((lo,hi))
        if a[i][1]<b[j][1]: i+=1
        else: j+=1
    return out


def compile_moves(data,length):
    verifier=verifier_for(data); moves=geometry_moves(data,length)
    numeric=lambda x:float(B.coerce(x).decimal())
    def quad(word,box):
        b,a,ts=quadratic_parameters(word,tuple(box))
        return [numeric(b),numeric(a),*map(numeric,ts)]
    result=[]
    for i,group in enumerate(moves):
        rb,sb,hb=verifier.box(i); compiled=[]
        for u,v,cases in group:
            cc=[]
            for swap,required,dests in cases:
                slopes={F(data['nodes'][j].get('scalar_slope','0')) for j in dests}
                if len(slopes)!=1:
                    break
                cuts={B.coerce(x) for x in required}
                cuts.update(B.coerce(x) for j in dests for x in verifier.box(j)[2]
                            if required[0]<x<required[1])
                cuts=sorted(cuts)
                strips=list(zip(cuts,cuts[1:])) or [(cuts[0],cuts[0])]
                groups=[[j for j in dests if verifier.box(j)[2][0]<=a<=b<=verifier.box(j)[2][1]]
                        for a,b in strips]
                cc.append([swap,float(next(iter(slopes))),groups])
            else:
                compiled.append([quad(u,rb),quad(v,sb),(-1)**len(u),(-1)**len(v),cc])
        result.append(dict(parity=data['nodes'][i]['parity'],hbox=list(map(numeric,hb)),
                           slope=float(F(data['nodes'][i].get('scalar_slope','0'))),
                           moves=compiled))
    return result


def qrange(q,k):
    b,inv,t0,t1=q; a=k*inv
    values=[(a*t+b)*t for t in (t0,t1)]
    if a:
        t=-b/(2*a)
        if t0<t<t1: values.append((a*t+b)*t)
    return min(values),max(values)


def endpoint(parent,move,swap,x,k):
    ql,qr,eu,ev,_=move; p=parent['parity']
    l=qrange(ql,p*ev*k if swap else eu*x)
    r=qrange(qr,ev*x if swap else p*eu*k)
    if p<0: r=(-r[1],-r[0])
    products=[h*(t-parent['slope']) for h in parent['hbox'] for t in r]
    return l[0]+min(products),l[1]+max(products)


def iterate(data,compiled,initial,rounds,limit=300000):
    grid=data['settings']['grid']; spans=[[tuple(x) for x in s] for s in initial['intervals']]
    history=[]; reason='round limit'
    for step in range(rounds):
        updated=[]
        for i,parent in enumerate(compiled):
            if not spans[i]: updated.append([]); continue
            offers=[]
            for move in parent['moves']:
                options=[]
                for swap,k,groups in move[4]:
                    common=None
                    for group in groups:
                        pieces=spans[group[0]] if len(group)==1 else merge(x for j in group for x in spans[j])
                        common=pieces if common is None else intersect(common,pieces)
                        if not common: break
                    cores=[]
                    for a,b in common or []:
                        if (parent['parity']*move[3] if swap else move[2])<0: a,b=b,a
                        lo=endpoint(parent,move,swap,a/grid,k)[1]
                        hi=endpoint(parent,move,swap,b/grid,k)[0]
                        if lo<hi: cores.append((lo,hi))
                    options.append(merge(cores))
                    if not options[-1]: break
                common=options[0]
                for pieces in options[1:]: common=intersect(common,pieces)
                offers.extend(common)
            rounded=merge((math.ceil(a*grid+1e-5),math.floor(b*grid-1e-5)) for a,b in merge(offers))
            updated.append(intersect(spans[i],rounded))
        stable=updated==spans; spans=updated
        row=dict(step=step+1,domains=sum(bool(s) for s in spans),components=sum(map(len,spans)),
                 root_components=[len(spans[j]) for j in data['roots']],stable=stable)
        history.append(row); print(json.dumps(row),flush=True)
        if stable or not any(spans): reason='stationary' if stable else 'empty'; break
        if row['components']>limit: reason='component limit'; break
    return dict(history=history,intervals=spans,reason=reason,closed=False,
                scope='floating discovery; only an exact closed verification is a proof')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path); ap.add_argument('--resume',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True); ap.add_argument('--cache',type=Path,required=True)
    ap.add_argument('--length',type=int,default=2); ap.add_argument('--rounds',type=int,default=30)
    args=ap.parse_args(); raw=args.source.read_bytes(); digest=hashlib.sha256(raw).hexdigest()
    data=json.loads(raw); initial=json.loads(args.resume.read_text())
    if initial['source_sha256']!=digest: raise ValueError('checkpoint source mismatch')
    if args.cache.exists():
        cache=json.loads(args.cache.read_text())
        if cache['source_sha256']!=digest or cache['length']!=args.length: raise ValueError('cache mismatch')
    else:
        cache=dict(source_sha256=digest,length=args.length,compiled=compile_moves(data,args.length))
        args.cache.write_text(json.dumps(cache,separators=(',',':'))+'\n')
    started=time.monotonic(); report=iterate(data,cache['compiled'],initial,args.rounds)
    report.update(source=str(args.source),source_sha256=digest,resumed_from=str(args.resume),elapsed_seconds=time.monotonic()-started)
    if report['reason']=='stationary' and any(report['intervals'][j] for j in data['roots']):
        try:
            result,exact=search(data,length=args.length,initial=dict(intervals=report['intervals'],history=[]),
                                iterations=2,allow_root_shrink=True,max_seconds=600,max_components=300000)
            report['exact_check']=exact; report['closed']=exact['closed']
            if result: args.output.with_suffix('.graph.json').write_text(json.dumps(result,indent=2)+'\n')
        except ValueError as error: report['exact_rejection']=str(error)
    args.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__': main()
