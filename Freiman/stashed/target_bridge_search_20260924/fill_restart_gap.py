#!/usr/bin/env python3
"""Target-directed exact search; partition only cylinders meeting remaining gaps."""
from pathlib import Path
from collections import deque
from fractions import Fraction as F
import argparse,json,sys,time
from search_restart_covers import l,verify,need
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'schecker_generalized'))
import explore as e

def compare(a,b):
    if isinstance(a,e.Q) and isinstance(b,e.Q):return (a-b).sign()
    if isinstance(a,l.K) and isinstance(b,l.K):return (a-b).sign()
    if isinstance(a,e.Q):return -compare(b,a)
    need(a.d==3,'quadratic endpoint field')
    A=l.K(a.a-b.a,a.b,3);c=-b.b
    sa=A.sign();sc=(c>0)-(c<0)
    if not sa:return sc
    if not sc or sa==sc:return sa
    return sa*(A*A-462*c*c).sign()

def K(d):return l.K(d['a'],d['b'],d['radicand'])
def subtract(gaps,lo,hi):
    out=[]
    for a,b in gaps:
        if hi<=a or b<=lo:out.append((a,b));continue
        if a<lo:out.append((a,min(b,lo)))
        if hi<b:out.append((max(a,hi),b))
    return out

def search(data,first,last,max_nodes,max_depth):
    root=tuple(data['root']);a=K(data['components'][first]['upper']);b=K(data['components'][last]['lower'])
    need(a<b,'gap band')
    target=(a,b);gaps=[target];offers=[]
    for comp in data['components']:
        for row in comp['chain']:
            lo,hi=K(row['lower']),K(row['upper']);offers.append((lo,hi,row))
            gaps=subtract(gaps,lo,hi)
    todo=deque([(0,*root)]);tested=0;pruned=0;limited=0;added=0
    while todo and gaps and tested<max_nodes:
        depth,u,v=todo.popleft();tested+=1
        cu,cv=e.cylinder(u),e.cylinder(v);lo=cu[0]+cv[0]+4;hi=cu[1]+cv[1]+4
        if not any(compare(lo,y)<0 and compare(x,hi)<0 for x,y in gaps):pruned+=1;continue
        unmarked=not any(w.endswith(('313','3131')) for w in (u,v))
        eligible=unmarked and (len(u)%2==len(v)%2 or not (u,v)[l.wider((u,v))].endswith('31'))
        if eligible:
            jl,jh=l.interval((u,v))
            if jl<jh and any(jl<y and x<jh for x,y in gaps):
                good=l.goodness((u,v))
                if l.K()<good:
                    row=dict(suffixes=[u[len(root[0]):],v[len(root[1]):]],lower=jl.json(),upper=jh.json(),goodness=good.json())
                    offers.append((jl,jh,row));gaps=subtract(gaps,jl,jh);added+=1
                    if not gaps:break
        if depth>=max_depth:limited+=1;continue
        side=0 if cv[1]-cv[0]<=cu[1]-cu[0] else 1
        for digit in '123':
            pair=[u,v];pair[side]+=digit
            if '31313' not in pair[side]:todo.append((depth+1,*pair))
    out=dict(status='COVER_FOUND' if not gaps else 'OPEN',root=root,target=[a.json(),b.json()],
        tested_nodes=tested,pruned=pruned,depth_limited=limited,queued=len(todo),new_good_covers=added,
        remaining=[[x.json(),y.json()] for x,y in gaps],limits=dict(nodes=max_nodes,depth=max_depth))
    if not gaps:
        pos=a;chain=[]
        while pos<b:
            candidates=[r for r in offers if r[0]<=pos<r[1]];need(bool(candidates),'strict certificate chain')
            row=max(candidates,key=lambda r:r[1]);chain.append(row[2]);pos=row[1]
        cert=dict(status='EXACT_LOCAL_RESTART_COVERS',family='custom',n=0,safe_mixed=True,root=root,
                  components=[dict(lower=K(chain[0]['lower']).json(),upper=pos.json(),chain=chain)])
        # The first chosen interval may start before the target; whole chain is certified.
        verify(cert);out['certificate']=cert
    return out

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--first',type=int,required=True)
    ap.add_argument('--last',type=int,required=True);ap.add_argument('--max-nodes',type=int,default=20000)
    ap.add_argument('--max-depth',type=int,default=24);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    start=time.monotonic();data=search(json.loads(args.input.read_text()),args.first,args.last,args.max_nodes,args.max_depth)
    data['seconds']=time.monotonic()-start;args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('certificate','target','remaining')},indent=2));print('remaining',len(data['remaining']),flush=True)
