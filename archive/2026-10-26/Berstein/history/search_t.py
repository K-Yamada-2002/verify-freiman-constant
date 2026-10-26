"""Exact local covers for the requested full-prefix forbidden-language T's.

Periodic CF endpoints are compared by rational isolation. Identical infinite
words (including different prefix/period spellings) share canonical keys.
Undecided comparisons fail closed. No local menu is labeled a closed proof.
"""
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
from exact_cf import cf
from exact_cf import interval as full_interval
from language import scan
from generalized_t import Language


@dataclass(frozen=True,order=True)
class Endpoint:
    pre:tuple
    period:tuple

    @staticmethod
    def make(pre,period):
        for n in range(1,len(period)+1):
            if len(period)%n==0 and period==period[:n]*(len(period)//n):
                period=period[:n];break
        while pre and pre[-1]==period[-1]:
            pre=pre[:-1];period=period[-1:]+period[:-1]
        return Endpoint(pre,period)

    @lru_cache(None)
    def bounds(self,n):
        w=self.pre+(self.period*(n//len(self.period)+1))[:n]
        return tuple(sorted(cf(w,t) for t in (Q(0),Q(1))))


@dataclass(frozen=True)
class Sum:
    terms:tuple

    @lru_cache(None)
    def bounds(self,n):
        out=[e.bounds(n) for e in self.terms]
        return sum(x for x,y in out),sum(y for x,y in out)

    def __float__(self):
        l,h=self.bounds(24)
        return float((l+h)/2)

    def data(self):
        return [dict(prefix=''.join(map(str,e.pre)),period=''.join(map(str,e.period))) for e in self.terms]


@lru_cache(None)
def ge(x,y):
    if x.terms==y.terms:return True
    for n in (24,64,160):
        xl,xh=x.bounds(n);yl,yh=y.bounds(n)
        if xl>=yh:return True
        if xh<yl:return False
    return False  # An unresolved algebraic equality cannot certify a cover.


@lru_cache(None)
def endpoint(lang,w,minimum):
    s=lang.scan(w)
    if s is None:return None
    pre,period=lang.extremal_tail(s,minimum==(len(w)%2==0))
    return Endpoint.make(w+pre,period)


@lru_cache(None)
def interval(U,V,L,R):
    channels=[]
    for A,B in ((L,R),(R,L)):
        ll=endpoint(A,U,True);rr=endpoint(B,V,True)
        if ll is None or rr is None:continue
        hi=Sum(tuple(sorted((endpoint(A,U,False),endpoint(B,V,False)))))
        channels.append((Sum(tuple(sorted((ll,rr)))),hi))
    if not channels:return None
    lowers=[a for a,b in channels];uppers=[b for a,b in channels]
    lo=next((a for a in lowers if all(ge(b,a) for b in lowers)),None)
    hi=next((a for a in uppers if all(ge(a,b) for b in uppers)),None)
    if lo is None or hi is None:
        raise ArithmeticError('Endpoint order unresolved; do not report an empty language')
    return lo,hi


def cover(parent,candidates):
    if ge(parent[0],parent[1]):
        return next(([c] for c in candidates if ge(parent[0],c['iv'][0])
                     and ge(c['iv'][1],parent[1])),None)
    reach=parent[0];chain=[]
    while not ge(reach,parent[1]):
        options=[c for c in candidates if ge(reach,c['iv'][0])
                 and ge(c['iv'][1],reach) and not ge(reach,c['iv'][1])]
        if not options:return None
        c=max(options,key=lambda c:float(c['iv'][1]))
        chain.append(c);reach=c['iv'][1]
    assert chain and ge(parent[0],chain[0]['iv'][0]) and ge(chain[-1]['iv'][1],parent[1])
    assert all(ge(x['iv'][1],y['iv'][0]) and ge(y['iv'][1],x['iv'][0]) for x,y in zip(chain,chain[1:]))
    return chain


@lru_cache(None)
def outer_gaps(U,V,depth):
    left=[U+u for u in product((1,2,3),repeat=depth) if scan(U+u) is not None]
    right=[V+v for v in product((1,2,3),repeat=depth) if scan(V+v) is not None]
    intervals=sorted(full_interval(u,v) for u in left for v in right)
    merged=[]
    for lo,hi in intervals:
        if merged and lo<=merged[-1][1]:merged[-1]=(merged[-1][0],max(merged[-1][1],hi))
        else:merged.append((lo,hi))
    return [(a[1],b[0]) for a,b in zip(merged,merged[1:])]


def obstructed(U,V,iv,depth):
    # If a true open gap intersects the interior of the proposed T interval,
    # that entire T can never be a recursively admissible interval.
    if not depth:return False
    lower=iv[0].bounds(48)[1];upper=iv[1].bounds(48)[0]
    return any(lower<b and a<upper for a,b in outer_gaps(U,V,depth))


def main():
    p=argparse.ArgumentParser();p.add_argument('--root',default='112,122')
    p.add_argument('--length',type=int,default=3);p.add_argument('--output',default='t_local.json')
    p.add_argument('--gap-depth',type=int,default=0)
    p.add_argument('--extra-depth',type=int,default=0,
                   help='Also try each individual extra forbidden word of length 2..N')
    p.add_argument('--pair-types',default='',help='Additional pairs such as binary+binary,no13+no31')
    args=p.parse_args();U,V=(tuple(map(int,w)) for w in args.root.split(','))
    base=((4,),(1,3,1))
    langs={name:Language(base+extra) for name,extra in
           [('F',()),('binary',((3,),)),('no13',((1,3),)),('no31',((3,1),)),
            ('no11',((1,1),)),('no33',((3,3),))]}
    for n in range(2,args.extra_depth+1):
        for w in product((1,2,3),repeat=n):
            if w==(1,3,1):continue
            name='no'+''.join(map(str,w))
            if name not in langs:langs[name]=Language(base+(w,))
    types={name:(lang,langs['F']) for name,lang in langs.items()}
    for name in filter(None,args.pair_types.split(',')):
        left,right=name.split('+');types[name]=(langs[left],langs[right])
    words={n:list(product((1,2,3),repeat=n)) for n in range(args.length+1)}
    candidates=[];rejected=0
    for n in range(1,args.length+1):
        for k in range(n+1):
            for u in words[k]:
                for v in words[n-k]:
                    for name,(L,R) in types.items():
                        iv=interval(U+u,V+v,L,R)
                        if iv:
                            if obstructed(U+u,V+v,iv,args.gap_depth):rejected+=1
                            else:candidates.append(dict(u=u,v=v,type=name,iv=iv))
    reports=[]
    for name,(L,R) in types.items():
        parent=interval(U,V,L,R)
        chain=cover(parent,candidates) if parent else None
        reports.append(dict(type=name,nonempty=parent is not None,
            covered=chain is not None,parent_endpoints=[t.data() for t in parent] if parent else None,
            menu=[dict(u=''.join(map(str,c['u'])),v=''.join(map(str,c['v'])),type=c['type'],
                       endpoints=[t.data() for t in c['iv']]) for c in chain] if chain else []))
    report=dict(root=args.root,maximum_total_extension=args.length,candidates=len(candidates),
        gap_audit_depth=args.gap_depth,extra_forbidden_depth=args.extra_depth,
        extra_pair_types=args.pair_types,excluded_by_true_gap=rejected,
        scope='Exact local covers only. Child admissibility and infinite closure are NOT certified.',
        proof_complete=False,types=reports)
    dest=Path(__file__).resolve().parents[1]/'data'/args.output
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(candidates=len(candidates),results=[(x['type'],x['nonempty'],x['covered'],len(x['menu'])) for x in reports])))

if __name__=='__main__':main()
