"""Uniform full-prefix generalized T input with past-3 flags and exact endpoints."""
import argparse,json
from fractions import Fraction as Q
from itertools import product
from math import isqrt
from pathlib import Path
from exact_cf import matrix,cf,tail_endpoint,parameters
from language import scan
from field_3_10 import E
from prepare import box

BASE=Path(__file__).resolve().parents[1];D=1<<48

def enclosing(x):
    x=E.cast(x);lo=hi=x.coeff[0];den=10**60
    for c,d in zip(x.coeff[1:],x.basis[1:]):
        z=isqrt(d*den*den);v=(c*Q(z,den),c*Q(z+1,den));lo+=min(v);hi+=max(v)
    lo*=D;hi*=D
    ans=lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator)
    assert Q(ans[0],D)<=x<=Q(ans[1],D)
    return ans

binary=(E.quad(Q(-1,2),Q(1,2),3),E.quad(-1,1,3))

def ends(a,u,lang):
    if lang and 3 in a+u:return None
    s=scan(a+u)
    if s is None:return None
    ts=binary if lang else [E.quad(v.a,v.b,10) for v in (tail_endpoint(s,True),tail_endpoint(s,False))]
    vv=sorted(cf(u,t) for t in ts)
    return tuple(vv if len(a)%2==0 else reversed(vv))

def prepare(args):
    m=args.memory;base=Q(args.base);low,high=args.low,args.high
    key=lambda a:(len(scan(a)),len(a)%2,3 in a,a[-m:])
    proto={}
    for n in range(m,m+3):
        for a in product((1,2,3),repeat=n):
            if scan(a) is not None:proto.setdefault(key(a),a)
    keys=sorted(proto);ids={k:i for i,k in enumerate(keys)}
    exts=[w for n in range(args.length+1) for w in product((1,2,3),repeat=n)]
    pairs={(i,j,0) for i,u in enumerate(exts) for j,v in enumerate(exts) if 0<len(u)+len(v)<=args.length}
    for u in ((1,2),(2,1)):
        if u not in exts:exts.append(u)
    pairs|={(exts.index(u),exts.index(v),0) for u in ((1,2),(2,1)) for v in ((1,2),(2,1))}
    pairs=sorted(pairs)
    anchor=lambda a:binary[len(a)%2]
    U,V=(tuple(map(int,w)) for w in args.root.split(','))
    r,s,rho=parameters(U,V);z=(1+r*anchor(U))/(1+s*anchor(V));S=rho*z*z
    rootbin=next(k for k in range(low,high+1) if base**k<=S<=base**(k+1))
    root=(ids[key(U)]*len(keys)+ids[key(V)])*(high-low+1)+rootbin-low
    for a,t in ((U,r),(V,s)):assert box(a,m)[0]<=t<=box(a,m)[1]
    lines=[f'BERSTEIN_T_GRAPH_V1 {len(keys)} {len(exts)} {low} {high} 5 {len(pairs)} {root}']
    lines+=[' '.join(map(str,p)) for p in pairs]
    lines+=[' '.join(map(str,enclosing(base**k))) for k in range(low,high+2)]
    constants={};checks=0
    for k in keys:
        a=proto[k];rb=box(a,m);x0=anchor(a)
        raw={x:i for i,x in enumerate(dict.fromkeys([x0]+[x for u in exts for lang in (0,1) for x in (ends(a,u,lang) or ())]))}
        # The old graph interface's width column is unused by this engine.
        lines += [f'{D} {D}',f'{len(a)%2} {enclosing(rb[0])[0]} {enclosing(rb[1])[1]} {raw[x0]} {len(raw)}']
        lines+=[' '.join(map(str,enclosing(x))) for x in raw]
        for u in exts:
            if scan(a+u) is None:lines.append('-1');continue
            child=ids[key(a+u)];cb=box(proto[key(a+u)],m)
            cr=sorted(cf(tuple(reversed(u)),t) for t in rb)
            assert cb[0]<=cr[0]<=cr[1]<=cb[1]
            A,B,C,F=matrix(u);zz=[(1+t*x0)/((C+t*A)*anchor(a+u)+F+t*B) for t in rb]
            fa=sorted(t*t for t in zz);constant=0
            if fa[0]==fa[1]:
                if fa[0] not in constants:constants[fa[0]]=len(constants)+1
                constant=constants[fa[0]]
            xx=[]
            for lang in (0,1):
                v=ends(a,u,lang);xx+= [-1,-1] if v is None else [raw[x] for x in v]
            lines.append(' '.join(map(str,[child,0,constant,enclosing(fa[0])[0],enclosing(fa[1])[1],0,D,0,D]+xx)))
            checks+=1
    out=BASE/'data'/args.name
    out.with_suffix('.dat').write_text('\n'.join(lines)+'\n')
    meta=dict(memory=m,base=str(base),low=low,high=high,length=args.length,anchor='binary_lower',
              keys=keys,prototypes=[proto[k] for k in keys],extensions=exts,pairs=pairs,
              types=['F','T_binary','L_binary','R_binary','B2'],root_words=[U,V],root=root,
              global_prefix_constraints=True,transition_checks=checks,interior_proved=False)
    out.with_suffix('.meta.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(dict(sides=len(keys),rows=len(keys)**2*(high-low+1)*5,checks=checks)))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--memory',type=int,default=2)
    p.add_argument('--length',type=int,default=2);p.add_argument('--base',default='11/10')
    p.add_argument('--low',type=int,default=-30);p.add_argument('--high',type=int,default=30)
    p.add_argument('--root',default='11222,12222');p.add_argument('--name',default='t_kernel')
    prepare(p.parse_args())
