#!/usr/bin/env python3
"""Create interval types by recombining endpoints learned from a finite proof.

The interval shapes are recomputed after each failed successor cover, within
each parameter cell. Only the endpoint pool is fixed during one run. This is
floating candidate discovery and does not certify infinite filledness.
"""
import argparse
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import subprocess
import tempfile

import invariant_boxes as ib
import invariant_endpoint_components as components
from adaptive_induction import verify


def install_pool(source):
    labels={tuple(z) for shape in source['types'] for z in shape}
    for a,h,b,k in labels:
        assert isinstance(a,str) and isinstance(b,str) and all(z in '123' for z in a+b)
        assert isinstance(h,bool) and isinstance(k,bool)
    labels.update(z[2:]+z[:2] for z in tuple(labels))
    labels.update(('',a,'',b) for a,b in product((False,True),repeat=2))

    @lru_cache(None)
    def records(s,t):
        points={}
        for a,h,b,k in sorted(labels):
            x,y=ib.tail_endpoint(s,a,h),ib.tail_endpoint(t,b,k)
            if x is None or y is None:continue
            points.setdefault((float(x.decimal()),float(y.decimal())),(a,h,b,k))
        return tuple(sorted(points.items()))

    @lru_cache(None)
    def learned_pool(s,t):
        return tuple(point for point,_ in records(s,t))

    components.pool=learned_pool
    components.mapped_pool.cache_clear()
    return records


def native_run(search,executable,rounds):
    """Export floating geometry only; exact certificate replay stays in Python."""
    pools=[];pool_ids={};maps=[];map_ids={}
    def pool_id(points):
        key=id(points)
        if key not in pool_ids:
            pool_ids[key]=len(pools);pools.append(points)
        return pool_ids[key]
    def map_id(ids):
        if ids not in map_ids:map_ids[ids]=len(maps);maps.append(ids)
        return map_ids[ids]
    encoded=[]
    for i,cell in enumerate(search.cells):
        s,t,p,qi=cell[:4];anchored=len(cell)==5
        if anchored:
            from invariant_anchor_components import anchor_float
            h=cell[4];alpha,beta=anchor_float(s,h),anchor_float(t,h if p>0 else not h)
        else:alpha=beta=0.
        header=(pool_id(components.pool(s,t)),int(anchored),p,
                *search.ranges[s],*search.ranges[t],*search.qboxes[qi],alpha,beta)
        moves=[(pool_id(mapped),[(cid,map_id(ids)) for cid,ids in deps])
               for _,_,deps,mapped in search.offers[i]]
        encoded.append((header,search.domains[i],search.order[i],moves))
    with tempfile.TemporaryDirectory(prefix='freiman-components-') as folder:
        inp,out=Path(folder)/'geometry.txt',Path(folder)/'result.json'
        with inp.open('w') as stream:
            def line(values):stream.write(' '.join(map(str,values))+'\n')
            line((len(pools),len(maps),len(encoded)))
            for points in pools:line((len(points),*(x for z in points for x in z)))
            for ids in maps:line((len(ids),*ids))
            for header,domain,order,moves in encoded:
                line(header);line((len(domain),*(x for pair in domain for x in pair)))
                line((len(order),*order));line((len(moves),))
                for pool,deps in moves:line((pool,len(deps),*(x for pair in deps for x in pair)))
        subprocess.run([str(executable.resolve()),str(inp),str(out),str(rounds)],check=True)
        raw=json.loads(out.read_text())
    history=raw['history']
    return {'status':'floating discovery only; requires exact verification',
            'nonempty_fixed_point':bool(raw['domains'] and history and not history[-1]['changed']),
            'history':history,
            'survivors':[{'cell':search.cells[row['cell']],
                          'endpoints':[list(components.pool(*search.cells[row['cell']][:2])[i])
                                       for pair in row['intervals'] for i in pair]}
                         for row in raw['domains']]}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--states',type=int,choices=(6,13),default=6)
    ap.add_argument('--bins',type=int,default=25)
    ap.add_argument('--base',type=float,default=.88)
    ap.add_argument('--rounds',type=int,default=40)
    ap.add_argument('--anchored',action='store_true',
                    help='use extremal derivative ratios and simultaneous six-digit returns')
    ap.add_argument('--native-executable',type=Path,
                    help='optional compiled learned_components_native.cpp accelerator')
    ap.add_argument('--extra-endpoints',type=Path,nargs='*',default=[],
                    help='additional candidate type banks; their filledness is never assumed')
    ap.add_argument('--extra-total-length',type=int,
                    help='optional discovery bound for the combined word length of extra endpoints')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    source=json.loads(args.certificate.read_text());verify(source)
    if 'cases' in source:
        source={'types':[shape for case in source['cases'] for shape in case['types']]}
    for extra in args.extra_endpoints:
        shapes=json.loads(extra.read_text())['types']
        if args.extra_total_length is not None:
            shapes=[[z for z in shape if len(z[0])+len(z[2])<=args.extra_total_length] for shape in shapes]
        source['types'].extend(shapes)
    if args.states==13:ib.STATES,ib.RANGES=ib.STATES13,ib.RANGES13
    records=install_pool(source)
    if args.anchored:
        # Import after installing the pool: the anchored search uses the
        # same learned endpoints in its return transitions as in its cells.
        from invariant_anchor_components import Anchored
        search=Anchored(args.bins,args.base,2)
    else:
        search=components.ComponentSearch(args.bins,args.base,2)
    print('prepared',len(search.cells),'cells;',
          max(len(components.pool(s,t)) for s in ib.STATES for t in ib.STATES),
          'maximum endpoints per state pair',flush=True)
    result=(native_run(search,args.native_executable,args.rounds) if args.native_executable
            else search.run(args.rounds))
    result['source_certificate']=str(args.certificate)
    result['settings']={'states':args.states,'bins':args.bins,'base':args.base,
                        'max_step':2,'rounds':args.rounds,
                        'anchored':args.anchored,
                        'engine':'native float' if args.native_executable else 'Python float',
                        'deduplicate_identical_components':True,
                        'extra_endpoint_banks':[str(p) for p in args.extra_endpoints],
                        'extra_total_length':args.extra_total_length,
                        'simultaneous_extremal_return':6 if args.anchored else None,
                        'shapes':'recombined adaptively from learned endpoint labels'}
    result['endpoint_pools']=[{'states':[s,t],'labels':[label for _,label in records(s,t)]}
                              for s in ib.STATES for t in ib.STATES]
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
