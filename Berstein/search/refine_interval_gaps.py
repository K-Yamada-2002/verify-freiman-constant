"""Try longer roots at the endpoints of the current certified components.

Exact outer hulls prune branches; a finite failed search is not a spectral gap
proof. Side widths only choose the branching order. Accepted rows still need
verify_interval_extensions.py. The original graph table is read only.
"""
import argparse
import json
import sys
from collections import deque
from fractions import Fraction as Q
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'Freiman/src'))
from exact_cf import K,interval,side_endpoint,union
from endpoint_return import ReturnSearch
from obstruction_probe import scan
sys.path.insert(0,str(ROOT/'Berstein/src'))
from explore_intervals import joined_bands
from spectral_rational import RationalBounds


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--nodes',type=int,default=4000)
    parser.add_argument('--length',type=int,default=16)
    args=parser.parse_args()
    source=ROOT/'Berstein/data/interval_extensions_candidates.json'
    data=json.loads(source.read_text())
    components=[tuple(K(*v) for v in iv) for iv in data['components']]
    kernel=ReturnSearch('graph_wide');kernel.name='graph_wide'
    spec=RationalBounds([(3,1,3,1,3)],backward=8)
    results=[];additions=[]
    for (_,start),(target,_) in zip(components,components[1:]):
        queue=deque([((3,),(4,))]);seen=set();processed=0;best=start;selected=[]
        while queue and processed<args.nodes:
            a,b=queue.popleft()
            if (a,b) in seen:continue
            seen.add((a,b));processed+=1
            L,H=interval(a,b)
            if 4+L>best or 4+H<=best:continue
            improved=False
            for row in joined_bands(kernel,a,b):
                l,h=(4+K(*v) for v in row['interval'])
                if not l<=best<h:continue
                # Extending fixed outward words restricts their tails. Thus
                # an already verified ancestor's all-position bound persists.
                ancestors=[r for r in data['rows'] if ''.join(map(str,a)).startswith(r['a'])
                           and ''.join(map(str,b)).startswith(r['b'])]
                if ancestors:
                    theta=min(K(*r['theta_upper']) for r in ancestors)
                else:
                    theta=K(Q(spec.root(a,b,4)['theta']))
                if theta>best:continue
                best=h
                accepted=dict(row,center=4,theta_upper=theta.data(),
                              covered_interval=[max(l,theta).data(),h.data()])
                selected.append(accepted)
                additions.append(accepted)
                print('EXTEND',float(start),row['a'],row['b'],float(best),flush=True)
                improved=True
                break
            if best>=target:break
            if improved:
                queue=deque([((3,),(4,))]);seen=set()
                continue
            if len(a)>=args.length and len(b)>=args.length:continue
            wa=side_endpoint(a,False)-side_endpoint(a,True)
            wb=side_endpoint(b,False)-side_endpoint(b,True)
            left=(wa>=wb and len(a)<args.length) or len(b)>=args.length
            for d in (1,2,3):
                aa,bb=(a+(d,),b) if left else (a,b+(d,))
                if scan(aa) is not None and scan(bb) is not None:
                    queue.append((aa,bb))
        results.append(dict(start=start.data(),target=target.data(),
                            best=best.data(),processed=processed,pending=len(queue),
                            selected=selected,connected=best>=target))
        print('BOUNDARY',float(start),'best',float(best),'nodes',processed,'pending',len(queue),flush=True)
    report=dict(scope='Bounded root refinement; failure is not a gap proof.',
                maximum_length=args.length,node_limit_per_boundary=args.nodes,results=results)
    (ROOT/'Berstein/data/interval_gap_refinement.json').write_text(json.dumps(report,indent=2)+'\n')
    if additions:
        data['rows']+=additions
        merged=union(tuple(K(*v) for v in row['covered_interval']) for row in data['rows'])
        data['components']=[[v.data() for v in iv] for iv in merged]
        data['components_decimal']=[[float(v) for v in iv] for iv in merged]
        data['refinement']=dict(maximum_length=args.length,node_limit_per_boundary=args.nodes)
        source.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
