"""Exact inputs for two experimental languages, separate from 131.

The graph format and closed-cover checker are shared with the original search.
Extrema lie in Q(sqrt(5)) for 313 and Q(sqrt(41667)) for 31313,13131.
No floating point is exported to the checker.
"""
import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
from field import E
from prepare import enclosing

BASE = Path(__file__).resolve().parents[1]
D = 1 << 48
BAD = (3,1,3)
BADS = (BAD,)
STATES = ((),(3,),(3,1))
RADICAND = 5


def configure(forbidden):
    """One language per process; exact quadratic field chosen explicitly."""
    global BADS,STATES,RADICAND
    BADS = tuple(tuple(map(int,w)) for w in forbidden.split(','))
    choices = {((3,1,3),):5, ((3,1,3,1,3),(1,3,1,3,1)):41667}
    assert BADS in choices, 'Unsupported exact extremal field'
    RADICAND = choices[BADS]
    STATES = tuple(sorted({w[:i] for w in BADS for i in range(len(w))}))
    E.basis = (1,2,RADICAND,2*RADICAND)
    E.__float__.cache_clear()
    scan.cache_clear()
    extremal_tail.cache_clear()
    tail_endpoint.cache_clear()


def step(state,d):
    w = state+(d,)
    if any(w[-len(b):] == b for b in BADS):
        return None
    return max((s for s in STATES if not s or w[-len(s):] == s), key=len)


@lru_cache(None)
def scan(w):
    s = ()
    for d in w:
        s = step(s,d)
        if s is None:
            return None
    return s


@lru_cache(None)
def matrix(w):
    a,b,c,d = 1,0,0,1
    for v in w:
        a,b,c,d = b,a+v*b,d,c+v*d
    return a,b,c,d


def cf(w,x):
    a,b,c,d = matrix(w)
    return (a*x+b)/(c*x+d)


@lru_cache(None)
def extremal_tail(state,minimum):
    seen = {}
    out = ()
    odd = True
    while (state,odd) not in seen:
        seen[state,odd] = len(out)
        choices = [d for d in (1,2,3) if step(state,d) is not None]
        # Every choice extends infinitely, e.g. by appending 2 forever.
        d = max(choices) if minimum == odd else min(choices)
        out += (d,)
        state,odd = step(state,d),not odd
    j = seen[state,odd]
    return out[:j],out[j:]


@lru_cache(None)
def tail_endpoint(state,minimum):
    pre,per = extremal_tail(state,minimum)
    a,b,c,d = matrix(per)
    disc = (d-a)**2+4*c*b
    factor = isqrt(disc//RADICAND)
    assert disc == RADICAND*factor*factor
    x = E.quad(Q(a-d,2*c),Q(factor,2*c),RADICAND)
    assert cf(per,x) == x and 0 < x < 1
    return cf(pre,x)


def ends(a,u=()):
    s = scan(a+u)
    assert s is not None
    low,high = sorted(cf(u,tail_endpoint(s,t)) for t in (True,False))
    return (low,high) if len(a)%2 == 0 else (high,low)


def side_interval(a):
    return tuple(sorted(cf(a,tail_endpoint(scan(a),t)) for t in (True,False)))


def parameters(a,b):
    _,_,pa,qa = matrix(a)
    _,_,pb,qb = matrix(b)
    return Q(pa,qa),Q(pb,qb),Q(qa*qa,qb*qb)


def shape(a,m):
    length = max(m,len(scan(a)))
    return tuple(sorted(cf(a[-length:][::-1],t) for t in (Q(1,4),Q(4,5))))


def prepare(args):
    configure(args.forbidden)
    m,L,n,grid = args.memory,args.length,args.spine,args.grid
    assert m>=2 and grid>1 and grid & (grid-1) == 0
    key = lambda a:(len(scan(a)),len(a)%2,a[-m:])
    proto = {}
    for k in range(m,max(m+1,max(map(len,BADS)))+1):
        for a in product((1,2,3),repeat=k):
            if scan(a) is not None:
                proto.setdefault(key(a),a)
    keys = sorted(proto)
    ids = {k:i for i,k in enumerate(keys)}
    exts = [u for k in range(L+1) for u in product((1,2,3),repeat=k)]
    pairs = {(i,j,0) for i,u in enumerate(exts) for j,w in enumerate(exts)
             if 0<len(u)+len(w)<=L}
    def spine(a):
        pre,per = extremal_tail(scan(a),len(a)%2 == 0)
        return (pre+per*(n+1))[:n]
    for a in proto.values():
        sp = spine(a)
        for k in range(n):
            for d in (1,2,3):
                u = sp[:k]+(d,)
                if u not in exts:
                    exts.append(u)
    unrestricted = {(i,j) for i,j,_ in pairs}
    pairs |= {(i,j,1) for i,u in enumerate(exts) for j,w in enumerate(exts)
              if 0<len(u)==len(w)<=n and (i,j) not in unrestricted}
    if args.return_length:
        returns=set()
        for a in proto.values():
            pre,per=extremal_tail(scan(a),len(a)%2==0)
            u=(pre+per*(args.return_length+1))[:args.return_length]
            if u not in exts:
                exts.append(u)
            returns.add(exts.index(u))
        # Exact equal derivative tags, not an assumed numerical equality,
        # decide whether the scale bin is preserved by these longer returns.
        pairs |= {(i,j,1) for i in returns for j in returns}
    pairs = sorted(pairs)
    bands = [(Q(0),Q(1))]+[(Q(i,grid),Q(i+2,grid)) for i in range(grid-1)]
    base,low,high = Q(args.base),args.low,args.high
    rootwords = tuple(tuple(map(int,w)) for w in args.root.split(','))
    a,b = rootwords
    r,s,rho = parameters(a,b)
    z = (1+r*ends(a)[0])/(1+s*ends(b)[0])
    S = rho*z*z
    rootbin = next(k for k in range(low,high+1) if base**k<=S<=base**(k+1))
    root = (ids[key(a)]*len(keys)+ids[key(b)])*(high-low+1)+rootbin-low
    lines = [f'FREIMAN_DYADIC_GRAPH_V1 {len(keys)} {len(exts)} {low} {high} {len(bands)} {len(pairs)} {root}']
    lines += [f'{int(l*D)} {int(h*D)}' for l,h in bands]
    lines += [' '.join(map(str,p)) for p in pairs]
    lines += [' '.join(map(str,enclosing(base**k))) for k in range(low,high+2)]
    constants = {}
    checks = 0
    for k in keys:
        a = proto[k]
        rb = shape(a,m)
        x0,x1 = ends(a)
        width = sorted((-1)**len(a)*(x1-x0)*(1+r*x0)/(1+r*x1) for r in rb)
        # Since the anchor is x0, width=(+/-)(x1-x0)(1+r*x0)/(1+r*x1).
        # This is monotone in r; both endpoints give its exact range.
        lines.append(f'{enclosing(width[0])[0]} {enclosing(width[1])[1]}')
        raw = {x:i for i,x in enumerate(dict.fromkeys(
            x for u in exts if scan(a+u) is not None for x in ends(a,u)))}
        lines.append(f'{len(a)%2} {enclosing(rb[0])[0]} {enclosing(rb[1])[1]} {raw[x0]} {len(raw)}')
        lines += [' '.join(map(str,enclosing(x))) for x in raw]
        for u in exts:
            if scan(a+u) is None:
                lines.append('-1')
                continue
            child = ids[key(a+u)]
            cr = tuple(sorted(cf(u[::-1],r) for r in rb))
            cb = shape(proto[key(a+u)],m)
            assert cb[0]<=cr[0]<=cr[1]<=cb[1]
            child_anchor = ends(a+u)[0]
            A,B,C,dd = matrix(u)
            ratios = [(1+r*x0)/((C+r*A)*child_anchor+dd+r*B) for r in rb]
            fa = sorted(v*v for v in ratios)
            constant = 0
            if fa[0] == fa[1]:
                if fa[0] not in constants:
                    constants[fa[0]] = len(constants)+1
                constant = constants[fa[0]]
            sp = int(bool(u) and len(u)<=n and u[:-1] == spine(a)[:len(u)-1])
            if args.return_length and len(u)==args.return_length:
                pre,per=extremal_tail(scan(a),len(a)%2==0)
                returning=(pre+per*(args.return_length+1))[:args.return_length]
                sp=int(u==returning)
            row = [child,sp,constant,enclosing(fa[0])[0],enclosing(fa[1])[1],
                   0,D,0,D]+[raw[x] for x in ends(a,u)]
            lines.append(' '.join(map(str,row)))
            checks += 1
    for w,ratio in zip(rootwords,parameters(*rootwords)[:2]):
        assert shape(w,m)[0]<=ratio<=shape(w,m)[1]
    path = BASE/'data'/args.name
    path.with_suffix('.dat').write_text('\n'.join(lines)+'\n')
    meta = dict(language=args.forbidden,forbidden=BADS,radicand=RADICAND,
                memory=m,length=L,spine=n,grid=grid,return_length=args.return_length,
                base=str(base),low=low,high=high,keys=keys,
                prototypes=[proto[k] for k in keys],extensions=exts,pairs=pairs,
                bands=[[str(x),str(y)] for x,y in bands],
                root_words=rootwords,root=root,root_bin=rootbin,root_scale=S.data(),
                transition_checks=checks,prehistory_interval=['1/4','4/5'],
                scope='Exact geometry only; a closed family and root check are required.')
    path.with_suffix('.meta.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(dict(sides=len(keys),extensions=len(exts),pairs=len(pairs),
                         rows=len(keys)**2*(high-low+1)*len(bands),checks=checks)),flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--memory',type=int,default=2)
    p.add_argument('--length',type=int,default=3)
    p.add_argument('--spine',type=int,default=6)
    p.add_argument('--grid',type=int,default=32)
    p.add_argument('--base',default='51/50')
    p.add_argument('--low',type=int,default=-140)
    p.add_argument('--high',type=int,default=140)
    p.add_argument('--root',default='112222,122222')
    p.add_argument('--name',default='avoid313_m2')
    p.add_argument('--forbidden',default='313')
    p.add_argument('--return-length',type=int,default=0)
    prepare(p.parse_args())
