"""Exact algebraic preparation for a dyadic-rational invariant-band kernel.

Every exported integer pair encloses its algebraic quantity, with denominator
2**48. Continued-fraction transition states and parameter-box inclusions are
checked exactly. No floating-point comparison is used by the verifier.
"""
import argparse,json
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
from math import isqrt
from typed_intervals import E
from typed_boxes import side_pairs
from obstruction_probe import scan
from box_certificates import suffix_range,child_box,contains
from anchor_boxes import anchor,derivative_fraction,delta_range
from width_catalog import normalized_difference_range
from exact_cf import parameters,matrix

BASE=DATA;SCALE=1<<48


def enclosing(value):
    value=E.cast(value);lo=hi=value.coeff[0];scale=10**50
    for c,d in zip(value.coeff[1:],(3,154,462)):
        z=isqrt(d*scale*scale);bounds=(c*Q(z,scale),c*Q(z+1,scale))
        lo+=min(bounds);hi+=max(bounds)
    a=lo*SCALE;b=hi*SCALE
    low=a.numerator//a.denominator;high=-((-b.numerator)//b.denominator)
    assert E.cast(Q(low,SCALE))<=value<=E.cast(Q(high,SCALE))
    return low,high


def prepare(source,name,graph=False,tight=False):
    meta=json.loads((BASE/(source+'.meta.json')).read_text());assert meta['coordinate']=='lower_endpoint_derivative_ratio'
    keys=[(q,p,tuple(s)) for q,p,s in meta['side_keys']];ids={k:i for i,k in enumerate(keys)}
    words=list(map(tuple,meta['prototypes']));exts=list(map(tuple,meta['extensions']))
    memory=meta['memory'];base=Q(meta['base']);low,high=meta['low'],meta['high'];n=meta['spine_depth']
    assert len(ids)==len(keys)==len(words) and memory>=1 and base>1 and low<high
    assert exts[0]==() and len(set(exts))==len(exts)
    assert all(d in (1,2,3) for u in exts for d in u)
    for key,word in zip(keys,words):
        state=scan(word)
        assert state is not None and len(word)>=memory
        assert key==(len(state),len(word)%2,word[-memory:])
    assert all(0<=i<len(exts) and 0<=j<len(exts) and flag in (0,1)
               for i,j,flag in meta['successor_pairs'])
    def suffix(word,length):
        if not tight:return suffix_range(word,length)
        a,b,c,d=matrix(tuple(reversed(word[-length:])))
        return tuple(sorted((a*t+b)/(c*t+d) for t in (Q(1,4),Q(4,5))))
    if tight:
        for digit in (1,2,3):
            assert Q(1,4)<=1/(digit+Q(4,5))<=1/(digit+Q(1,4))<=Q(4,5)
    from obstruction_probe import extremal_tail
    types=[('F',Q(0),Q(1))]+[(name,Q(a),1-Q(b)) for name,kind,a,b in meta['type_data'] if kind==5]
    assert all((x*SCALE).denominator==1 and (y*SCALE).denominator==1 for _,x,y in types)
    assert all(len(exts[i])+len(exts[j])>0 for i,j,_ in meta['successor_pairs'])
    # Verify the root's bin and cylinder coordinates without logarithms/floats.
    aa,bb=(3,2,1,1,3),(4,3,2,2);r,s,rho=parameters(aa,bb)
    z=(1+r*anchor(aa))/(1+s*anchor(bb));root_scale=rho*z*z
    root_bin=meta['root_geometry_id']%(high-low+1)+low
    assert base**root_bin<=root_scale<=base**(root_bin+1)
    ia=ids[(len(scan(aa)),len(aa)%2,aa[-memory:])]
    ib=ids[(len(scan(bb)),len(bb)%2,bb[-memory:])]
    assert meta['root_geometry_id']//(high-low+1)==ia*len(keys)+ib
    assert contains((suffix(words[ia],max(memory,len(scan(aa)))),),( (r,r),))
    assert contains((suffix(words[ib],max(memory,len(scan(bb)))),),( (s,s),))
    magic='FREIMAN_DYADIC_GRAPH_V1' if graph else 'FREIMAN_DYADIC_V1'
    lines=[f'{magic} {len(keys)} {len(exts)} {low} {high} {len(types)} {len(meta["successor_pairs"])} {meta["root_geometry_id"]}']
    lines.extend(f'{int(a*SCALE)} {int(b*SCALE)}' for _,a,b in types)
    lines.extend(' '.join(map(str,p)) for p in meta['successor_pairs'])
    lines.extend(' '.join(map(str,enclosing(base**i))) for i in range(low,high+2))
    constants={};count=0
    for key,a in zip(keys,words):
        rb=suffix(a,max(memory,key[0]));x0=anchor(a);x1=side_pairs(scan(a),len(a)%2,(),'base')[1]
        ww=delta_range(x0,x1,x0,rb)
        if len(a)%2:ww=(-ww[1],-ww[0])
        lines.append(f'{enclosing(ww[0])[0]} {enclosing(ww[1])[1]}')
        raw={}
        if graph:
            for u in exts:
                if scan(a+u) is not None:
                    for value in side_pairs(scan(a),len(a)%2,u,'base'):
                        if value not in raw:raw[value]=len(raw)
            lines.append(f'{len(a)%2} {enclosing(rb[0])[0]} {enclosing(rb[1])[1]} {raw[x0]} {len(raw)}')
            lines.extend(' '.join(map(str,enclosing(value))) for value in raw)
        pre,period=extremal_tail(scan(a),len(a)%2==0);sp=(pre+period*(n+1))[:n]
        for u in exts:
            if scan(a+u) is None:lines.append('-1');continue
            childkey=(len(scan(a+u)),len(a+u)%2,(a+u)[-memory:]);child=ids[childkey]
            newrb=child_box((rb,(Q(0),Q(0)),(Q(1),Q(1))),u,())[0]
            assert contains((suffix(words[child],max(memory,childkey[0])),),(newrb,))
            fa=derivative_fraction(a,u,rb)
            constant=0
            if fa[0]==fa[1]:
                if fa[0] not in constants:constants[fa[0]]=len(constants)+1
                constant=constants[fa[0]]
            on_spine=bool(u) and len(u)<=n and u[:-1]==sp[:len(u)-1]
            eta=[]
            for x in side_pairs(scan(a),len(a)%2,u,'base'):
                vs=normalized_difference_range(scan(a),x,x0,rb)
                if len(a)%2:vs=(-vs[1],-vs[0])
                ll,hh=enclosing(vs[0])[0],enclosing(vs[1])[1]
                # The full cylinder inclusions also give 0 <= eta <= 1.
                eta.extend((max(0,ll),min(SCALE,hh)))
            extra=[raw[x] for x in side_pairs(scan(a),len(a)%2,u,'base')] if graph else []
            lines.append(' '.join(map(str,[child,int(on_spine),constant,enclosing(fa[0])[0],enclosing(fa[1])[1]]+eta+extra)))
            assert 0<=eta[0]<=eta[1]<=SCALE and 0<=eta[2]<=eta[3]<=SCALE
            count+=1
    (BASE/(name+'.dat')).write_text('\n'.join(lines)+'\n')
    meta.update(types=[t[0] for t in types],bands=[[str(a),str(b)] for _,a,b in types],
                scale=SCALE,arithmetic='Integer interval arithmetic with denominator 2^48',
                preparation_checks=count,source_numerical_universe=source)
    meta['prehistory_interval']=['1/4','4/5'] if tight else ['0','1']
    (BASE/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({'exact_transition_checks':count,'states':len(keys)**2*(high-low+1)*len(types)}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('--name',default='certified_kernel')
    p.add_argument('--graph',action='store_true');p.add_argument('--tight',action='store_true');a=p.parse_args()
    prepare(a.source,a.name,a.graph,a.tight)
