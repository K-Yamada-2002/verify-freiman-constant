"""Discover spectral bridges using bands, without a full-hull gap filter.

Floating point is used only to shortlist roots. Every accepted interval is
computed in Q(sqrt(462)) and clipped by an all-position spectral bound.
"""
import json
from functools import lru_cache
from fractions import Fraction as Q
from exact_cf import K, CF, interval, parameters, matrix, union
from endpoint_return import ReturnSearch, BASE
from anchor_boxes import anchor
from obstruction_probe import scan
from spectral_bounds import bound_root


@lru_cache(None)
def side_id(kernel, word):
    key = (len(scan(word)), len(word) % 2, word[-kernel.memory:])
    if key not in kernel.ids:
        return None
    sid = kernel.ids[key]
    length = max(kernel.memory, key[0])
    proto = tuple(kernel.meta['prototypes'][sid])
    aa, bb, cc, dd = matrix(tuple(reversed(proto[-length:])))
    bounds = sorted((aa*t+bb)/(cc*t+dd) for t in
                    map(Q, kernel.meta.get('prehistory_interval', ['0','1'])))
    _, _, c, d = matrix(word)
    return sid if bounds[0] <= Q(c,d) <= bounds[1] else None


def point_bands(kernel, a, b):
    ia, ib = side_id(kernel,a), side_id(kernel,b)
    if ia is None or ib is None:
        return []
    r,s,rho = parameters(a,b)
    z = (1+r*anchor(a))/(1+s*anchor(b))
    S = rho*z*z
    i = kernel.index(S)
    if not kernel.low <= i <= kernel.high:
        return []
    assert kernel.base**i <= S <= kernel.base**(i+1)
    geom = ia*kernel.sides+ib
    return [(p,q,{'kernel':kernel.name,'geometry':geom,'bin':i,'type':typ})
            for typ,p,q in kernel.bands
            if ((geom*kernel.bins+i-kernel.low)*kernel.T+typ) in kernel.alive]


def decode(components):
    return [tuple(K(*z) for z in iv) for iv in components]


def main():
    kernels=[]
    for name in ('graph_m2','graph_wide'):
        k=ReturnSearch(name); assert k.certified; k.name=name; kernels.append(k)
    base=json.loads((BASE/'endpoint_closure_verified.json').read_text())
    pieces=decode(base['certified_markov_components'])
    pieces+=decode(json.loads((BASE/'wide_root_intervals.json').read_text())['components'])
    pieces=union(pieces)
    gaps=list(zip([v[1] for v in pieces[:-1]],[v[0] for v in pieces[1:]]))
    fgaps=[(float(l),float(h)) for l,h in gaps]
    pool={};spectral={}
    for name in ('root_inventory_depth11','root_inventory_center3','augmented_roots'):
        data=json.loads((BASE/(name+'.json')).read_text())
        for row in data.get('candidate_roots',[]):
            pool[row['a'],row['b'],row['center']]=row
        for row in data['selected_roots']:
            spectral[row['a'],row['b'],row['center']]=row
    accepted=[];tested=0
    for key,row in sorted(pool.items(),key=lambda item:len(item[0][0])+len(item[0][1])):
        fl,fh=row['screen_interval']
        if not any(fl<h and l<fh for l,h in fgaps):continue
        a,b=tuple(map(int,key[0])),tuple(map(int,key[1])); center=key[2]
        L,H=interval(a,b); candidates=[]
        for kernel in kernels:
            for p,q,proof in point_bands(kernel,a,b):
                lo,hi=center+L+p*(H-L),center+L+q*(H-L)
                if any(lo<h and l<hi for l,h in gaps):
                    candidates.append((lo,hi,p,q,proof))
        if not candidates:continue
        if key not in spectral:
            spectral[key]=bound_root(a,b,center)
        theta=K(*spectral[key]['theta_upper']); tested+=1
        additions=[]
        for lo,hi,p,q,proof in candidates:
            lo=max(lo,theta,CF)
            if lo<=hi and any(lo<h and l<hi for l,h in gaps):
                additions.append({'band':[str(p),str(q)],'interval':[lo.data(),hi.data()],**proof})
                pieces.append((lo,hi))
        if additions:
            accepted.append({'a':key[0],'b':key[1],'center':center,
                             'spectral':spectral[key],'bands':additions})
            pieces=union(pieces)
            gaps=list(zip([v[1] for v in pieces[:-1]],[v[0] for v in pieces[1:]]))
            fgaps=[(float(l),float(h)) for l,h in gaps]
            print(json.dumps({'root':key,'components':len(pieces),'gaps':fgaps}),flush=True)
            if not gaps:break
    result={'passed':True,'scope':'Certified finite band union; no full-hull assertion.',
            'base_sources':['endpoint_closure_verified.json','wide_root_intervals.json'],
            'spectral_roots_tested':tested,'accepted':accepted,
            'components':[[v.data() for v in iv] for iv in pieces],
            'gaps':[[v.data() for v in iv] for iv in gaps],
            'components_decimal':[[float(v) for v in iv] for iv in pieces],
            'freiman_to_sqrt21':len(pieces)==1 and pieces[0][0]==CF and pieces[0][1]*pieces[0][1]>=21}
    (BASE/'bridge_bands.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='accepted'},indent=2),flush=True)


if __name__=='__main__':main()
