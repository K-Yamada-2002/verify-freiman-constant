"""Independent semantics audit for the two interior-interval tail languages.

The raw input parser is included here. The generators and
their arithmetic/automata are not imported. Checks include raw endpoint aliases,
constant derivative identities, and every child shape inclusion.
"""
import argparse
import copy
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache,total_ordering
from math import isqrt
from pathlib import Path


RAD = 5


@total_ordering
@dataclass(frozen=True)
class Exact:
    a: Q = Q(0)
    b: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self,'a',Q(self.a))
        object.__setattr__(self,'b',Q(self.b))
    @staticmethod
    def cast(x):
        return x if isinstance(x,Exact) else Exact(x)
    def __add__(self,x):
        x=self.cast(x)
        return Exact(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self):return Exact(-self.a,-self.b)
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x)
        return Exact(self.a*x.a+RAD*self.b*x.b,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def __truediv__(self,x):
        x=self.cast(x)
        norm=x.a*x.a-RAD*x.b*x.b
        return self*Exact(x.a/norm,-x.b/norm)
    def __rtruediv__(self,x):return self.cast(x)/self
    def __eq__(self,x):
        x=self.cast(x)
        return (self.a,self.b)==(x.a,x.b)
    def __lt__(self,x):
        v=self-x
        if not v.b:return v.a<0
        if not v.a:return v.b<0
        if (v.a>0)==(v.b>0):return v.a<0
        return v.a*v.a<RAD*v.b*v.b if v.a>0 else v.a*v.a>RAD*v.b*v.b


def cf(word,x):
    for d in word[::-1]:x=1/(d+x)
    return x


def matrix(word):
    z=((1,0),(0,1))
    for d in word:
        z=((z[0][1],z[0][0]+d*z[0][1]),(z[1][1],z[1][0]+d*z[1][1]))
    return *z[0],*z[1]


def contains(iv,child):return iv[0]<=child[0]<=child[1]<=iv[1]
def encloses(iv,x):return iv[0]<=x<=iv[1]


def audit(data,meta):
    bad=tuple(tuple(w) for w in meta['forbidden'])
    prefixes=tuple(sorted({w[:i] for w in bad for i in range(len(w))}))
    def legal(w):
        return not any(w[i:i+len(b)]==b for b in bad for i in range(len(w)-len(b)+1))
    def state(w):
        if not legal(w):return None
        return max((s for s in prefixes if not s or w[-len(s):]==s),key=len)
    @lru_cache(None)
    def cycle(s,minimum):
        seen={};out=();odd=True
        while (s,odd) not in seen:
            seen[s,odd]=len(out)
            choices=[d for d in (1,2,3) if legal(s+(d,))]
            d=max(choices) if minimum==odd else min(choices)
            out+=(d,);s=state(s+(d,));odd=not odd
        i=seen[s,odd]
        return out[:i],out[i:]
    @lru_cache(None)
    def extreme(s,minimum):
        pre,per=cycle(s,minimum)
        a,b,c,d=matrix(per)
        disc=(d-a)**2+4*b*c
        f=isqrt(disc//RAD)
        assert disc==RAD*f*f
        root=Exact(Q(a-d,2*c),Q(f,2*c))
        assert 0<root<1 and cf(per,root)==root
        out=cf(pre,root)
        w=pre+(per*101)[:100]
        assert encloses(sorted(cf(w,t) for t in (Q(0),Q(1))),out)
        return out
    keys=[(q,p,tuple(w)) for q,p,w in meta['keys']]
    ids={k:i for i,k in enumerate(keys)}
    words=[tuple(w) for w in meta['prototypes']]
    exts=[tuple(w) for w in meta['extensions']]
    memory=meta['memory']
    assert data['s']==len(keys)==len(ids)==len(words)
    assert data['e']==len(exts)==len(set(exts)) and exts[0]==()
    assert data['pairs']==[tuple(p) for p in meta['pairs']]
    assert all(0<=i<len(exts) and 0<=j<len(exts) and f in (0,1)
               and len(exts[i])+len(exts[j])>0 for i,j,f in data['pairs'])
    assert data['low']==meta['low'] and data['high']==meta['high']
    base=Q(meta['base'])
    for i,iv in zip(range(data['low'],data['high']+2),data['powers']):assert encloses(iv,base**i)
    grid=meta['grid']
    assert data['bands']==[(Q(0),Q(1))]+[(Q(i,grid),Q(i+2,grid)) for i in range(grid-1)]
    prehistory=tuple(map(Q,meta['prehistory_interval']))
    assert prehistory==(Q(1,4),Q(4,5))
    for d in (1,2,3):assert contains(prehistory,sorted(1/(d+x) for x in prehistory))
    shapes=[];anchors=[];states=[]
    for (q,p,suffix),w,side in zip(keys,words,data['sides']):
        s=state(w)
        assert s is not None and len(s)==q and len(w)%2==p and w[-memory:]==suffix
        assert side['parity']==p
        defining=s if q>memory else suffix
        assert w[-max(memory,q):]==defining
        shape=tuple(sorted(cf(defining[::-1],x) for x in prehistory))
        assert contains(side['shape'],shape)
        shapes.append(shape);states.append(s);anchors.append(extreme(s,p==0))
    constants={};transitions=aliases=0
    for i,side in enumerate(data['sides']):
        q,p,suffix=keys[i]
        assigned={}
        pre,per=cycle(states[i],p==0)
        n=meta['spine'];spine=(pre+per*(n+1))[:n]
        for u,record in zip(exts,side['extensions']):
            childstate=state(states[i]+u)
            if childstate is None:
                assert record is None
                continue
            assert record is not None
            j=ids[(len(childstate),(p+len(u))%2,(suffix+u)[-memory:])]
            assert record['child']==j
            expected_spine=bool(u) and len(u)<=n and u[:-1]==spine[:len(u)-1]
            returning=meta.get('return_length',0)
            if returning and len(u)==returning:
                expected_spine=u==(pre+per*(returning+1))[:returning]
            # Earlier unrestricted trial files did not mark long returns;
            # their added pairs carry flag 0 and do not consult this flag.
            if returning and len(u)==returning and all(flag==0 for a,b,flag in data['pairs']
                                 if len(exts[a])==len(exts[b])==returning):
                expected_spine=False
            assert record['spine']==int(expected_spine)
            endpoints=sorted(cf(u,extreme(childstate,t)) for t in (True,False))
            if p:endpoints.reverse()
            for x,raw in zip(endpoints,record['endpoints']):
                assert 0<=raw<len(side['tails']) and encloses(side['tails'][raw],x)
                if raw in assigned:
                    assert assigned[raw]==x
                    aliases+=1
                assigned[raw]=x
            a,b,c,d=matrix(u)
            newshape=tuple(sorted((c+r*a)/(d+r*b) for r in shapes[i]))
            assert contains(shapes[j],newshape)
            x,y=anchors[i],anchors[j]
            v0,v1=c*y+d,a*y+b
            assert v0>0 and v1>=0
            determinant=x*v0-v1
            values=[]
            for r in shapes[i]:
                v=(1+r*x)/(v0+r*v1)
                values.append(v*v)
                assert encloses(record['scale'],v*v)
            constant=record['constant']
            assert bool(constant)==(determinant==0)
            if constant:
                assert values[0]==values[1]==1/(v0*v0)
                if constant in constants:assert constants[constant]==values[0]
                constants[constant]=values[0]
            transitions+=1
        assert len(assigned)==len(side['tails'])
        assert len(set(assigned.values()))==len(assigned)
        assert assigned[side['anchor']]==anchors[i]
        assert side['extensions'][0]['endpoints'][0]==side['anchor']
    assert len(set(constants.values()))==len(constants)
    return dict(passed=True,transitions=transitions,endpoint_alias_checks=aliases,
                constant_groups=len(constants),language=meta['language'],radicand=RAD)


DEN = 1 << 48

def demand(condition, message):
    if not condition:
        raise AssertionError(message)

def parse_input(path):
    tokens = iter(path.read_text().split())
    demand(next(tokens) == 'FREIMAN_DYADIC_GRAPH_V1', 'Input magic')

    def integer():
        return int(next(tokens))

    def interval():
        lo, hi = Q(integer(), DEN), Q(integer(), DEN)
        demand(lo <= hi, 'Reversed input interval')
        return lo, hi

    s, e, low, high, types, pairs, root = [integer() for _ in range(7)]
    data = dict(s=s, e=e, low=low, high=high, types=types, root=root)
    data['bands'] = [interval() for _ in range(types)]
    data['pairs'] = [tuple(integer() for _ in range(3)) for _ in range(pairs)]
    data['powers'] = [interval() for _ in range(high - low + 2)]
    data['sides'] = []
    for _ in range(s):
        width = interval()
        parity, shape, anchor = integer(), interval(), integer()
        tails = [interval() for _ in range(integer())]
        extensions = []
        for _ in range(e):
            child = integer()
            if child < 0:
                demand(child == -1, 'Invalid absent-child marker')
                extensions.append(None)
            else:
                spine, constant = integer(), integer()
                scale, eta = interval(), [interval(), interval()]
                endpoints = [integer(), integer()]
                extensions.append(dict(child=child, spine=spine, constant=constant,
                                       scale=scale, eta=eta, endpoints=endpoints))
        data['sides'].append(dict(width=width, parity=parity, shape=shape,
                                  anchor=anchor, tails=tails, extensions=extensions))
    demand(next(tokens, None) is None, 'Unparsed trailing input')
    return data



def main():
    if not __debug__:
        raise RuntimeError('Verification requires Python assertions; do not use -O')
    global RAD
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('metadata', type=Path)
    args = parser.parse_args()
    meta = json.loads(args.metadata.read_text())
    RAD = meta['radicand']
    data = parse_input(args.input)
    report = audit(data, meta)
    controls = []
    for name in ('alias', 'constant', 'endpoint'):
        damaged = copy.deepcopy(data)
        record = damaged['sides'][0]['extensions'][0]
        if name == 'alias':
            record['endpoints'][1] = record['endpoints'][0]
        elif name == 'constant':
            record = next(r for s in damaged['sides'] for r in s['extensions'] if r and not r['constant'])
            record['constant'] = 1
        else:
            damaged['sides'][0]['tails'][0] = (Q(0), Q(0))
        try:
            audit(damaged, meta)
        except AssertionError:
            controls.append(name)
        else:
            raise AssertionError('Corruption accepted: ' + name)
    report['negative_controls'] = controls
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
