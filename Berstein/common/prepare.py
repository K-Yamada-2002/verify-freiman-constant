"""Certified Q(sqrt(10)) input for the uniform successor-cover search.

Adapted from Freiman's graph-kernel interface, independently instantiated for
131 avoidance. All geometry exported to C++ is enclosed in dyadic rationals.
"""
import argparse
import json
from fractions import Fraction as Q
from itertools import product
from math import isqrt
from pathlib import Path
from exact_cf import K, cf, matrix, parameters, tail_endpoint
from language import scan, extremal_tail
from field import E

BASE = Path(__file__).resolve().parents[1]
D = 1 << 48

def enclosing(x):
    x = E.cast(x)
    den = 10**60
    lo = hi = x.coeff[0]
    for c,d in zip(x.coeff[1:],x.basis[1:]):
        z = isqrt(d*den*den)
        lo += min(c*Q(z,den),c*Q(z+1,den))
        hi += max(c*Q(z,den),c*Q(z+1,den))
    lo, hi = lo*D, hi*D
    ans = lo.numerator//lo.denominator, -((-hi.numerator)//hi.denominator)
    assert Q(ans[0],D) <= x <= Q(ans[1],D)
    return ans

def ends(a, u=()):
    s = scan(a+u)
    assert s is not None
    lo, hi = sorted(E.quad(v.a,v.b,10) for v in (cf(u,tail_endpoint(s,t)) for t in (True,False)))
    return (lo,hi) if len(a)%2==0 else (hi,lo)

def box(a,m):
    return tuple(sorted(cf(tuple(reversed(a[-m:])),x) for x in (Q(1,4),Q(4,5))))

def prepare(args):
    m,L,n,grid = args.memory,args.length,args.spine,args.grid
    centered=args.centered
    def anchor(a):
        if args.anchor=='golden':return E.quad(Q(-1,2),Q(1,2),5)
        if args.anchor=='silver':return E.quad(-1,1,2)
        return ends(a)[0]
    assert m>=2 and grid>1 and grid&(grid-1)==0
    key = lambda a: (len(scan(a)),len(a)%2,a[-m:])
    proto = {}
    if args.shape_tolerance:
        tolerance=Q(args.shape_tolerance)
        assert tolerance>0
        pending=list(product((1,2,3),repeat=m));leaves=set()
        while pending:
            a=pending.pop()
            if scan(a) is None:continue
            lo,hi=box(a,len(a))
            if hi-lo<=tolerance:leaves.add(a)
            else:
                if len(a)>=args.max_suffix:raise ValueError('Increase --max-suffix')
                pending.extend((d,)+a for d in (1,2,3))
        def key(a):
            tail=next((a[-n:] for n in range(m,len(a)+1) if a[-n:] in leaves),None)
            if tail is None:raise ValueError('Root is too short for the adaptive suffix cover')
            return len(scan(a)),len(a)%2,tail
        for suffix in sorted(leaves):
            for a in (suffix,(2,)+suffix):proto.setdefault(key(a),a)
    else:
        for k in (m,m+1):
            for a in product((1,2,3),repeat=k):
                if scan(a) is not None: proto.setdefault(key(a),a)
    shape=lambda a:box(a,len(key(a)[2]))
    keys=sorted(proto); ids={k:i for i,k in enumerate(keys)}
    exts=[u for k in range(L+1) for u in product((1,2,3),repeat=k)]
    pairs={(i,j,0) for i,u in enumerate(exts) for j,w in enumerate(exts) if 0<len(u)+len(w)<=L}
    def spine(a):
        pre,per=extremal_tail(scan(a),len(a)%2==0)
        return (pre+per*(n+1))[:n]
    for a in proto.values():
        sp=spine(a)
        for k in range(n):
            for d in (1,2,3):
                u=sp[:k]+(d,)
                if u not in exts: exts.append(u)
    unrestricted={(i,j) for i,j,_ in pairs}
    pairs |= {(i,j,1) for i,u in enumerate(exts) for j,w in enumerate(exts)
              if 0<len(u)==len(w)<=n and (i,j) not in unrestricted}
    pairs=sorted(pairs)
    bands=[(Q(0),Q(1))]+[(Q(i,grid),Q(i+2,grid)) for i in range(grid-1)]
    if centered:bands=[(x-Q(1,2),y-Q(1,2)) for x,y in bands]
    base=Q(args.base); low,high=args.low,args.high
    rootwords=tuple(tuple(map(int,w)) for w in args.root.split(','))
    a,b=rootwords
    r,s,rho=parameters(a,b)
    root_scale=rho*((1+r*anchor(a))/(1+s*anchor(b)))*((1+r*anchor(a))/(1+s*anchor(b)))
    rootbin=next(k for k in range(low,high+1) if base**k<=root_scale<=base**(k+1))
    root=(ids[key(a)]*len(keys)+ids[key(b)])*(high-low+1)+rootbin-low
    magic='BERSTEIN_ANCHOR_GRAPH_V1' if centered else 'FREIMAN_DYADIC_GRAPH_V1'
    lines=[f'{magic} {len(keys)} {len(exts)} {low} {high} {len(bands)} {len(pairs)} {root}']
    lines += [f'{int(l*D)} {int(h*D)}' for l,h in bands]
    lines += [' '.join(map(str,p)) for p in pairs]
    lines += [' '.join(map(str,enclosing(base**k))) for k in range(low,high+2)]
    constants={};checks=0
    for k in keys:
        a=proto[k]; rb=shape(a); xlo,x1=ends(a); x0=anchor(a)
        # Safe independent bounds for positive derivative-normalized widths.
        width=sorted((-1)**len(a)*(x1-xlo)*((1+r*x0)/(1+r*xlo))*((1+s*x0)/(1+s*x1)) for r in rb for s in rb)
        lines.append(f'{enclosing(width[0])[0]} {enclosing(width[1])[1]}')
        def coordinates(u):
            if centered:
                value=cf(u,anchor(a+u))
                return value,value
            return ends(a,u)
        raw={x:i for i,x in enumerate(dict.fromkeys([x0]+[x for u in exts if scan(a+u) is not None for x in coordinates(u)]))}
        lines.append(f'{len(a)%2} {enclosing(rb[0])[0]} {enclosing(rb[1])[1]} {raw[x0]} {len(raw)}')
        lines += [' '.join(map(str,enclosing(x))) for x in raw]
        for u in exts:
            if scan(a+u) is None:
                lines.append('-1');continue
            child=ids[key(a+u)]
            cr=tuple(sorted(cf(tuple(reversed(u)),r) for r in rb))
            cb=shape(proto[key(a+u)])
            assert cb[0]<=cr[0]<=cr[1]<=cb[1]
            child_anchor=anchor(a+u); A,B,C,dd=matrix(u)
            vals=[(1+r*x0)/((C+r*A)*child_anchor+dd+r*B) for r in rb]
            fa=sorted(v*v for v in vals)
            c=0
            if fa[0]==fa[1]:
                if fa[0] not in constants: constants[fa[0]]=len(constants)+1
                c=constants[fa[0]]
            sp=int(bool(u) and len(u)<=n and u[:-1]==spine(a)[:len(u)-1])
            # eta is unused by the overlap graph; export a certified [0,1].
            row=[child,sp,c,enclosing(fa[0])[0],enclosing(fa[1])[1],0,D,0,D]+[raw[x] for x in coordinates(u)]
            lines.append(' '.join(map(str,row))); checks+=1
    rr,ss,_=parameters(*rootwords)
    for w,t in zip(rootwords,(rr,ss)):
        assert shape(w)[0]<=t<=shape(w)[1]
    path=BASE/'data'/args.name
    path.with_suffix('.dat').write_text('\n'.join(lines)+'\n')
    meta=dict(memory=m,length=L,spine=n,grid=grid,anchor=args.anchor,centered=centered,base=str(base),low=low,high=high,
              shape_tolerance=args.shape_tolerance,max_suffix=args.max_suffix,
              keys=keys,prototypes=[proto[k] for k in keys],extensions=exts,pairs=pairs,
              bands=[[str(x),str(y)] for x,y in bands],root_words=rootwords,root=root,
              root_bin=rootbin,root_scale=root_scale.data(),transition_checks=checks,
              scope='Rigorous local geometry; interior only after nonempty closure and root membership.')
    path.with_suffix('.meta.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(dict(sides=len(keys),extensions=len(exts),pairs=len(pairs),
                         rows=len(keys)**2*(high-low+1)*len(bands),checks=checks)))

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--memory',type=int,default=2)
    p.add_argument('--length',type=int,default=3)
    p.add_argument('--spine',type=int,default=4)
    p.add_argument('--grid',type=int,default=32)
    p.add_argument('--base',default='11/10')
    p.add_argument('--anchor',choices=['lower','golden','silver'],default='lower')
    p.add_argument('--centered',action='store_true')
    p.add_argument('--shape-tolerance')
    p.add_argument('--max-suffix',type=int,default=8)
    p.add_argument('--low',type=int,default=-24)
    p.add_argument('--high',type=int,default=24)
    p.add_argument('--root',default='11222,12222')
    p.add_argument('--name',default='m2')
    prepare(p.parse_args())
