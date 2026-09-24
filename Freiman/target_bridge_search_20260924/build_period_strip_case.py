#!/usr/bin/env python3
"""Find a literal strip from a fixed restart to its next periodic copy."""
from pathlib import Path
import json,argparse,time
from search_restart_covers import search as pool_search,l,need,verify
from fill_restart_gap import search as gap_search,K
HERE=Path(__file__).resolve().parent

def components(rows):
    rows=sorted(rows,key=lambda r:K(r['lower']));out=[]
    for row in rows:
        lo,hi=K(row['lower']),K(row['upper'])
        if not out or K(out[-1]['upper'])<lo:out.append(dict(lower=lo.json(),upper=hi.json(),chain=[row]))
        else:
            out[-1]['chain'].append(row)
            if K(out[-1]['upper'])<hi:out[-1]['upper']=hi.json()
    return out

def row(root,ws):
    pair=tuple(a+b for a,b in zip(root,ws));lo,hi=l.interval(pair);g=l.goodness(pair)
    need(l.K()<g and lo<hi,'period strip anchor is good')
    need(len(pair[0])%2==len(pair[1])%2 or not pair[l.wider(pair)].endswith('31'),'restart anchor guard')
    return dict(suffixes=ws,lower=lo.json(),upper=hi.json(),goodness=g.json())

def build(n,m):
    root=('3211'+'313121'*n+'33'+'131213'*m,'4322'+'313121'*n+'131312'*m)
    start=('','11');finish=('131213','13131211')
    first,last=row(root,start),row(root,finish)
    data=pool_search(n,2,root,6,True)
    rows=[r for c in data['components'] for r in c['chain']]+[first,last]
    data['components']=components(rows)
    ia=next(i for i,c in enumerate(data['components']) if K(c['lower'])<=K(first['lower'])<=K(c['upper']))
    ib=next(i for i,c in enumerate(data['components']) if K(c['lower'])<=K(last['upper'])<=K(c['upper']))
    stats={}
    if ia!=ib:
        bridge=gap_search(data,ia,ib,20000,32)
        need(bridge['status']=='COVER_FOUND','literal periodic strip remains open')
        stats={k:bridge[k] for k in ('tested_nodes','new_good_covers','seconds') if k in bridge}
        rows.extend(r for c in bridge['certificate']['components'] for r in c['chain'])
    target_lo,target_hi=K(first['lower']),K(last['upper']);pos=K(first['upper']);chain=[first]
    # Finish on the prescribed periodic copy, rather than an unrelated longer interval.
    while pos<K(last['lower']):
        choices=[r for r in rows if K(r['lower'])<=pos<K(r['upper'])]
        need(bool(choices),'assembled strip contact')
        r=max(choices,key=lambda r:K(r['upper']));chain.append(r);pos=K(r['upper'])
    if chain[-1]['suffixes']!=finish:chain.append(last)
    # Greedy steps may overshoot the last cover: the component keeps the maximum.
    upper=max(K(r['upper']) for r in chain);lower=min(K(r['lower']) for r in chain)
    return dict(status='LITERAL_PERIOD_STRIP',n=n,m=m,root=root,first=start,last=finish,
                chain=[r['suffixes'] for r in chain],rows=chain,search_stats=stats,
                scope='Literal finite-index cover; uniformity must be checked separately')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,required=True);ap.add_argument('--m',type=int,required=True);a=ap.parse_args()
    start=time.monotonic();d=build(a.n,a.m);d['seconds']=time.monotonic()-start
    (HERE/f'period_strip_n{a.n}_m{a.m}.json').write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps({k:v for k,v in d.items() if k!='rows'},indent=2))
