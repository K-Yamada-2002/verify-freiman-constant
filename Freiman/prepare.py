"""Exact arithmetic and reproducible input for the Freiman Hall-ray table.

The saved metadata specifies a finite universe of states, extensions and bands.
Every exported dyadic endpoint encloses an exact algebraic expression. This
module also supplies the continued-fraction and box arithmetic used by proof.py.
Only Python's standard library is required.
"""
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache, total_ordering
from math import isqrt, gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCALE = 1 << 48


# Persistent 31313 language

DIGITS = (1, 2, 3)


BAD = (3, 1, 3, 1, 3)


STATES = tuple(BAD[:i] for i in range(len(BAD)))


def step(state, digit):
    word = state + (digit,)
    if word[-len(BAD):] == BAD:
        return None
    return max((s for s in STATES if not s or word[-len(s):] == s), key=len)


def scan(word):
    state = ()
    for digit in word:
        state = step(state, digit)
        if state is None:
            return None
    return state


@lru_cache(None)
def extremal_tail(state, minimize):
    # Alternating lexicographic order of continued fractions. Every allowed
    # digit has an infinite continuation (append 2 forever), so greedy is exact.
    seen, word, odd = {}, [], True
    while (state, odd) not in seen:
        seen[state, odd] = len(word)
        allowed = [d for d in DIGITS if step(state, d) is not None]
        digit = max(allowed) if minimize == odd else min(allowed)
        word.append(digit)
        state, odd = step(state, digit), not odd
    cut = seen[state, odd]
    return tuple(word[:cut]), tuple(word[cut:])

# Exact Q(sqrt(462)) and continued fractions

@total_ordering
@dataclass(frozen=True)
class K:
    a: Q = Q(0)
    b: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', Q(self.a))
        object.__setattr__(self, 'b', Q(self.b))

    @staticmethod
    def cast(x):
        return x if isinstance(x, K) else K(x)

    def __add__(self, other):
        other = self.cast(other)
        return K(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        return K(self.a * other.a + 462 * self.b * other.b,
                 self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        norm = other.a * other.a - 462 * other.b * other.b
        if not norm:
            raise ZeroDivisionError
        return self * K(other.a / norm, -other.b / norm)

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def sign(self):
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        comp = a * a - 462 * b * b
        return ((comp > 0) - (comp < 0)) * (1 if a > 0 else -1)

    def __eq__(self, other):
        try:
            other = self.cast(other)
        except (TypeError, ValueError):
            return False
        return self.a == other.a and self.b == other.b

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __float__(self):
        return float(self.a) + float(self.b) * 462**0.5

    def data(self):
        return [str(self.a), str(self.b)]


@lru_cache(None)
def matrix(word):
    a, b, c, d = 1, 0, 0, 1
    for v in word:
        a, b, c, d = b, a + v * b, d, c + v * d
    return a, b, c, d


def cf(word, tail):
    a, b, c, d = matrix(tuple(word))
    return (a * tail + b) / (c * tail + d)


@lru_cache(None)
def periodic(word):
    a, b, c, d = matrix(tuple(word))
    disc = (d - a)**2 + 4 * c * b
    factor = isqrt(disc // 462)
    assert 462 * factor * factor == disc, (word, disc)
    return K(Q(a - d, 2 * c), Q(factor, 2 * c))


@lru_cache(None)
def tail_endpoint(state, minimize):
    pre, period = extremal_tail(state, minimize)
    return cf(pre, periodic(period))


@lru_cache(None)
def side_endpoint(word, minimize):
    state = scan(word)
    if state is None:
        raise ValueError('Forbidden word')
    return cf(word, tail_endpoint(state, minimize == (len(word) % 2 == 0)))


@lru_cache(None)
def interval(a, b):
    return (side_endpoint(a, True) + side_endpoint(b, True),
            side_endpoint(a, False) + side_endpoint(b, False))


def denominators(word):
    _, _, c, d = matrix(tuple(word))
    return d, c


def parameters(a, b):
    qa, pa = denominators(a)
    qb, pb = denominators(b)
    return Q(pa, qa), Q(pb, qb), Q(qa * qa, qb * qb)


CF = K(Q(2221564096, 491993569), Q(283748, 491993569))


def union(intervals):
    result = []
    for lo, hi in sorted(intervals):
        assert lo <= hi
        if result and lo <= result[-1][1]:
            result[-1] = (result[-1][0], max(result[-1][1], hi))
        else:
            result.append((lo, hi))
    return result

# Exact endpoint expressions

@total_ordering
@dataclass(frozen=True)
class E:
    coeff: tuple=(Q(0),Q(0),Q(0),Q(0))
    basis=(1,3,154,462)

    def __post_init__(self):object.__setattr__(self,'coeff',tuple(map(Q,self.coeff)))
    @staticmethod
    def cast(x):return x if isinstance(x,E) else E((Q(x),0,0,0))
    @staticmethod
    def quad(a,b,d):
        out=[Q(a),Q(0),Q(0),Q(0)];out[E.basis.index(d)]=Q(b);return E(tuple(out))
    def __add__(self,x):return E(tuple(a+b for a,b in zip(self.coeff,self.cast(x).coeff)))
    __radd__=__add__
    def __neg__(self):return E(tuple(-x for x in self.coeff))
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        other=self.cast(x);out=[Q(0)]*4
        for i,a in enumerate(self.coeff):
            if not a:continue
            for j,b in enumerate(other.coeff):
                if not b:continue
                g=gcd(self.basis[i],self.basis[j]);rad=self.basis[i]*self.basis[j]//(g*g)
                out[self.basis.index(rad)]+=a*b*g
        return E(tuple(out))
    __rmul__=__mul__
    def __truediv__(self,x):
        other=self.cast(x);irr=[i for i in range(1,4) if other.coeff[i]]
        if not irr:return E(tuple(c/other.coeff[0] for c in self.coeff))
        if len(irr)>1:raise ValueError('Only single-quadratic inverses are required')
        i=irr[0];a=other.coeff[0];b=other.coeff[i]
        norm=a*a-self.basis[i]*b*b
        inv=[Q(0)]*4;inv[0]=a/norm;inv[i]=-b/norm
        return self*E(tuple(inv))
    def __rtruediv__(self,x):return self.cast(x)/self
    def sign(self):
        if not any(self.coeff):return 0
        nonzero=[i for i in range(1,4) if self.coeff[i]]
        if not nonzero:return (self.coeff[0]>0)-(self.coeff[0]<0)
        if len(nonzero)==1:
            i=nonzero[0];a,b=self.coeff[0],self.coeff[i]
            if not a or (a>0)==(b>0):return 1 if b>0 else -1
            t=a*a-self.basis[i]*b*b
            return ((t>0)-(t<0))*(1 if a>0 else -1)
        scale=10**12
        while True:
            lo=hi=self.coeff[0]
            for i in nonzero:
                z=isqrt(self.basis[i]*scale*scale)
                v=[self.coeff[i]*Q(z,scale),self.coeff[i]*Q(z+1,scale)]
                lo+=min(v);hi+=max(v)
            if lo>0:return 1
            if hi<0:return -1
            scale*=scale
    def __eq__(self,x):
        try:return self.coeff==self.cast(x).coeff
        except (TypeError,ValueError):return False
    def __lt__(self,x):return (self-x).sign()<0
    @lru_cache(maxsize=50000)
    def __float__(self):
        # Some derivative ratios have huge conjugates: summing floating
        # coefficients could return a negative number for a positive value.
        # Refine rational radical enclosures until both round to one float.
        if not any(self.coeff[1:]):return float(self.coeff[0])
        scale=10**32
        while True:
            lo=hi=self.coeff[0]
            for c,d in zip(self.coeff[1:],self.basis[1:]):
                if not c:continue
                q=isqrt(d*scale*scale)
                vals=(c*Q(q,scale),c*Q(q+1,scale))
                lo+=min(vals);hi+=max(vals)
            ll,hh=float(lo),float(hi)
            if ll==hh:return ll
            scale*=scale
    def data(self):return [str(x) for x in self.coeff]


BINARY=(E.quad(Q(-1,2),Q(1,2),3),E.quad(-1,1,3))


@lru_cache(None)
def endpoints(state,kind):
    if kind=='binary':return BINARY
    return tuple(E.quad(v.a,v.b,462) for v in (tail_endpoint(state,True),tail_endpoint(state,False)))


def channels(kind):
    if kind=='F':return (('base','base'),)
    if kind=='T2':return (('binary','base'),('base','binary'))
    if kind=='L2':return (('binary','base'),)
    if kind=='R2':return (('base','binary'),)
    if kind=='B2':return (('binary','binary'),)
    raise ValueError(kind)

# Suffix boxes and one-sided images

@lru_cache(None)
def side_pairs(state,parity,word,lang):
    for d in word:
        state=step(state,d)
        if state is None:raise ValueError('Forbidden child')
    values=sorted(cf(word,t) for t in endpoints(state,lang))
    return tuple(values if not parity else reversed(values))

# Continuant ratios

def suffix_range(word,n):
    suffix=tuple(reversed(word[-n:]))
    a,b,c,d=matrix(suffix)
    vals=[Q(a*t+b,c*t+d) for t in (0,1)]
    return min(vals),max(vals)


def child_box(box,u,w):
    def one(bounds,word):
        a,b,c,d=matrix(word)
        vals=[(c+r*a)/(d+r*b) for r in bounds]
        growth=[d+r*b for r in bounds]
        return (min(vals),max(vals)),(min(growth),max(growth))
    rr,qa=one(box[0],u);ss,qb=one(box[1],w)
    rho=(box[2][0]*(qa[0]/qb[1])**2,box[2][1]*(qa[1]/qb[0])**2)
    return (rr,ss,rho)


def contains(outer,inner):
    return all(lo<=ll and hh<=hi for (lo,hi),(ll,hh) in zip(outer,inner))

# Normalization at the lower endpoint

@lru_cache(maxsize=100000)
def delta_range(anchor,x,y,bounds):
    factor=x-y
    if factor==0:return E.cast(0),E.cast(0)
    A=2*anchor-x-y;B=anchor*(x+y)-2*x*y
    vals=[A+B*r for r in bounds]
    def value(r):return factor*((1+r*anchor)/(1+r*x))*((1+r*anchor)/(1+r*y))
    if min(vals)>=0 or max(vals)<=0:
        vs=[value(r) for r in bounds]
    else:
        aa=[(1+r*anchor)/(1+r*x) for r in bounds]
        bb=[(1+r*anchor)/(1+r*y) for r in bounds]
        vs=[factor*a*b for a in aa for b in bb]
    return min(vs),max(vs)


def anchor(word):return side_pairs(scan(word),len(word)%2,(),'base')[0]


@lru_cache(maxsize=30000)
def derivative_fraction(word,ext,bounds):
    x=anchor(word);y=anchor(word+ext);a,b,c,d=matrix(ext)
    vals=[]
    for r in bounds:
        z=(1+r*x)/((c+r*a)*y+d+r*b);vals.append(z*z)
    return min(vals),max(vals)

# Width-normalized differences

@lru_cache(maxsize=20000)
def normalized_difference_range(state,x,y,bounds):
    m,M=endpoints(state,'base');lo,hi=bounds
    factor=(x-y)/(M-m)
    if factor==0:return E.cast(0),E.cast(0)
    def value(r):return factor*((1+r*m)/(1+r*x))*((1+r*M)/(1+r*y))
    # Derivative of ((1+r*m)(1+r*M))/((1+r*x)(1+r*y)).
    S,P=m+M,m*M;T,V=x+y,x*y
    A,B,C=S-T,2*(P-V),P*T-V*S
    bern=(A+B*lo+C*lo*lo,
          A+B*lo+C*lo*lo+(hi-lo)*(B+2*C*lo)/2,
          A+B*hi+C*hi*hi)
    if all(v>=0 for v in bern) or all(v<=0 for v in bern):
        vals=[value(lo),value(hi)];return min(vals),max(vals)
    # A product enclosure remains rigorous when the derivative changes sign.
    left=[(1+r*m)/(1+r*x) for r in bounds]
    right=[(1+r*M)/(1+r*y) for r in bounds]
    vals=[factor*a*b for a in left for b in right]
    return min(vals),max(vals)

# Outward rounding to the dyadic input format

def enclosing(value):
    value=E.cast(value);lo=hi=value.coeff[0];scale=10**50
    for c,d in zip(value.coeff[1:],(3,154,462)):
        z=isqrt(d*scale*scale);bounds=(c*Q(z,scale),c*Q(z+1,scale))
        lo+=min(bounds);hi+=max(bounds)
    a=lo*SCALE;b=hi*SCALE
    low=a.numerator//a.denominator;high=-((-b.numerator)//b.denominator)
    assert E.cast(Q(low,SCALE))<=value<=E.cast(Q(high,SCALE))
    return low,high

# Complete finite-table input

def prepare(metadata, output):
    """Recompute every numeric record from a finite-universe description."""
    graph = True
    source = "graph_wide"
    meta = json.loads(Path(metadata).read_text())
    tight = meta.get("prehistory_interval") == ["1/4", "4/5"]
    assert tight, "The current Freiman certificate uses the invariant prehistory box"
    assert meta['coordinate']=='lower_endpoint_derivative_ratio'
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
    Path(output).with_suffix('.dat').write_text('\n'.join(lines)+'\n')
    assert meta['types'] == [t[0] for t in types]
    assert meta['bands'] == [[str(a),str(b)] for _,a,b in types]
    assert meta['scale'] == SCALE and meta['preparation_checks'] == count
    Path(output).with_suffix('.meta.json').write_text(json.dumps(meta,indent=2)+'\n')
    return {'exact_transition_checks': count,
            'candidate_rows': len(keys)**2*(high-low+1)*len(types)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata', type=Path, default=HERE / 'certificates/graph_wide.meta.json')
    parser.add_argument('--output', required=True, type=Path,
                        help='Output prefix for .dat and .meta.json')
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Exact input checks require assertions; do not use -O')
    print(json.dumps(prepare(args.metadata, args.output), indent=2))


if __name__ == '__main__':
    main()
