"""Assemble a finite certificate from closed-kernel bands and the endpoint.

This is discovery only. verify_hall_ray.py rechecks a fixed certificate.
No Schecker or Freiman interval tables are imported.
"""
import json
import argparse
from itertools import product
from functools import lru_cache
from fractions import Fraction as Q
from bridge_search import ReturnSearch, BASE, K, CF, point_bands, interval
from root_search import core_max, word_info
from spectral_bounds import bound_root


@lru_cache(None)
def words_of_length(n):
    return [w for w in product((1,2,3,4),repeat=n) if word_info(w)]


def bridge_point(kernels,current,spectral,max_total=12):
    """Shortlist with floats; accept only exact membership and domination."""
    x=float(current)
    for total in range(4,max_total+1):
        candidates=[];screened=0
        for h in range(1,min(6,total//2)+1):
            k=total-h
            if k>6:continue
            for a in words_of_length(h):
                la,ha,_,qa,_=word_info(a)
                for b in words_of_length(k):
                    if h==k and b<a:continue
                    lb,hb,_,qb,_=word_info(b)
                    if not 1/200 < (qa/qb)**2 < 200:continue
                    for c in (3,4,5):
                        if not c+la+lb-1e-12<=x<c+ha+hb+1e-12:continue
                        if core_max(a,b,c)>x+1e-12:continue
                        screened+=1
                        for row in joined_bands(kernels,a,b):
                            lo,hi=(K(*z)+c for z in row['interval'])
                            if lo<=current<hi:candidates.append((hi,{**row,'center':c}))
        for hi,row in sorted(candidates,key=lambda v:v[0],reverse=True):
            key=row['a'],row['b'],row['center']
            if key not in spectral:
                spectral[key]=bound_root(tuple(map(int,key[0])),tuple(map(int,key[1])),key[2])
            if K(*spectral[key]['theta_upper'])<=current:
                print('NEW ROOT',key,'depth',total,'screened',screened,flush=True)
                return row
        print('SEARCH POINT',x,'depth',total,'screened',screened,'candidates',len(candidates),flush=True)
    return None


def joined_bands(kernels,a,b):
    bands=[v for k in kernels for v in point_bands(k,a,b)]
    result=[]
    for p,q,proof in sorted(bands,key=lambda v:(v[0],v[1])):
        if result and p<=result[-1][1]:
            result[-1][1]=max(q,result[-1][1])
            result[-1][2].append({'band':[str(p),str(q)],**proof})
        else:result.append([p,q,[{'band':[str(p),str(q)],**proof}]])
    L,H=interval(a,b)
    return [{'a':''.join(map(str,a)),'b':''.join(map(str,b)),
             'band':[str(p),str(q)],'interval':[(L+p*(H-L)).data(),(L+q*(H-L)).data()],
             'proofs':proofs} for p,q,proofs in result]


def greedy(rows,start,target,spectral=None):
    current=start;selected=[];cache={} if spectral is None else spectral
    while current<target:
        candidates=[]
        for row in rows:
            lo,hi=(K(*z) for z in row['interval'])
            c=row.get('center',0);lo+=c;hi+=c
            if hi<=current or lo>current:continue
            key=row['a'],row['b'],c
            if c:
                if key in cache:lo=max(lo,K(*cache[key]['theta_upper']))
                elif row['screen_theta']>float(current)+1e-12:continue
            if lo<=current:candidates.append((hi,row))
        if not candidates:
            print('STOP',float(current),flush=True);return selected,current,cache
        hi,row=max(candidates,key=lambda z:z[0]);c=row.get('center',0)
        key=row['a'],row['b'],c
        if c and key not in cache:
            cache[key]=bound_root(tuple(map(int,row['a'])),tuple(map(int,row['b'])),c)
            continue
        result={k:v for k,v in row.items() if k!='screen_theta'}
        lo=K(*row['interval'][0])+c
        if c:
            result['theta_upper']=cache[key]['theta_upper'];lo=max(lo,K(*result['theta_upper']))
        assert lo<=current<hi
        result['covered_interval']=[lo.data(),hi.data()]
        selected.append(result);current=hi
        print('CHOOSE',c,row['a'],row['b'],row['band'],float(current),flush=True)
    return selected,current,cache


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--regenerate-template',action='store_true')
    args=parser.parse_args()
    kernels=[]
    for name in ('graph_m2','graph_wide'):
        k=ReturnSearch(name);k.name=name;assert k.certified;kernels.append(k)
    template=BASE/'upper_four_sum_bands.json'
    if args.regenerate_template or not template.exists():
        words=[w for n in range(1,4) for w in words_of_length(n)]
        upper=[row for i,a in enumerate(words) for b in words[i:]
               for row in joined_bands(kernels,a,b)]
        template.write_text(json.dumps({'rows':upper},indent=2)+'\n')
    else:
        upper=json.loads(template.read_text())['rows']
    translated,end,_=greedy(upper,K(Q(1,2)),K(Q(3,2)))
    assert end>=K(Q(3,2))
    pool={};spectral={}
    for name in ('augmented_roots','bridge_bands'):
        data=json.loads((BASE/(name+'.json')).read_text())
        for row in data.get('selected_roots',[])+[v['spectral'] for v in data.get('accepted',[])]:
            key=row['a'],row['b'],row['center'];spectral[key]=row
            pool[key]=joined_bands(kernels,tuple(map(int,key[0])),tuple(map(int,key[1])))
    rows=[]
    for key,bands in pool.items():
        rows.extend({**row,'center':key[2]} for row in bands)
    for row in upper:
        a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        for c in (4,5):
            rows.append({**row,'center':c,'screen_theta':core_max(a,b,c)})
    endpoint=json.loads((BASE/'endpoint_closure_verified.json').read_text())
    start=K(*endpoint['endpoint_markov_interval'][1])
    finite,end,spectral=greedy(rows,start,K(Q(13,2)),spectral)
    while end<K(Q(13,2)):
        new=bridge_point(kernels,end,spectral)
        if new is None:break
        rows.append(new)
        following,end,spectral=greedy(rows,end,K(Q(13,2)),spectral)
        finite+=following
    result={'discovery_complete':end>=K(Q(13,2)),
            'endpoint_source':'endpoint_closure_verified.json',
            'endpoint_interval':endpoint['endpoint_markov_interval'],
            'finite_chain':finite,'finite_chain_end':end.data(),
            'translation_chain':translated,'translation_target':['1/2','3/2'],
            'translation_centers':'all integers >= 6',
            'spectral_roots':[spectral[key] for key in sorted({(v['a'],v['b'],v['center']) for v in finite})]}
    (BASE/'hall_ray_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('COMPLETE',result['discovery_complete'],'finite',len(finite),'translation',len(translated),flush=True)


if __name__=='__main__':main()
