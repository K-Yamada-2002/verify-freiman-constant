"""Discover fixed root bands for a closed 313-avoiding graph table.

Floats only screen candidates. Selected root intervals, bins, shape membership,
and all-position bounds are checked exactly before inclusion in the output.
"""
import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
from field import E
from prepare_313 import configure, scan, matrix, cf, parameters, tail_endpoint, ends, side_interval, shape
from spectral_rational import RationalBounds

BASE = Path(__file__).resolve().parents[1]


def union(intervals):
    out = []
    for l,h in sorted(intervals):
        if out and l<=out[-1][1]:
            out[-1] = out[-1][0],max(out[-1][1],h)
        else:
            out.append((l,h))
    return out


class Table:
    def __init__(self,name):
        self.name = name
        self.meta = json.loads((BASE/'data'/f'{name}.meta.json').read_text())
        report = json.loads((BASE/'data'/f'{name}.json').read_text())
        assert report['closed_family_found']
        configure(self.meta['language'])
        word_info.cache_clear()
        self.bits = (BASE/'data'/f'{name}.json.alive.bin').read_bytes()
        m = self.meta
        self.ids = {(q,p,tuple(s)):i for i,(q,p,s) in enumerate(m['keys'])}
        self.powers = [Q(m['base'])**i for i in range(m['low'],m['high']+2)]
        self.B = len(self.powers)-1
        self.T = len(m['bands'])
        assert len(self.bits) == len(self.ids)**2*self.B*self.T

    @lru_cache(None)
    def side_id(self,w):
        key = len(scan(w)),len(w)%2,w[-self.meta['memory']:]
        sid = self.ids.get(key)
        if sid is None:
            return None
        proto = tuple(self.meta['prototypes'][sid])
        l,h = shape(proto,self.meta['memory'])
        _,_,p,q = matrix(w)
        return sid if l<=Q(p,q)<=h else None

    def rows(self,a,b):
        ia,ib = self.side_id(a),self.side_id(b)
        if ia is None or ib is None:
            return []
        r,s,rho = parameters(a,b)
        z = (1+r*ends(a)[0])/(1+s*ends(b)[0])
        S = rho*z*z
        index = self.scale_bin(S)
        if index is None:
            return []
        geom = ia*len(self.ids)+ib
        available = [(Q(l),Q(h),t) for t,(l,h) in enumerate(self.meta['bands'])
                     if self.bits[(geom*self.B+index)*self.T+t]]
        merged = []
        for l,h,t in sorted(available):
            if merged and l<=merged[-1][1]:
                merged[-1][1] = max(merged[-1][1],h)
                merged[-1][2].append(t)
            else:
                merged.append([l,h,[t]])
        aa,bb = side_interval(a),side_interval(b)
        L,H = aa[0]+bb[0],aa[1]+bb[1]
        return [dict(a=''.join(map(str,a)),b=''.join(map(str,b)),
                     band=[str(l),str(h)],types=types,geometry=geom,
                     bin=index+self.meta['low'],
                     interval=[(L+l*(H-L)).data(),(L+h*(H-L)).data()])
                for l,h,types in merged]

    def scale_bin(self,S):
        # Choose the first closed bin, including the lower one at a grid cut,
        # exactly as the original exhaustive scan did.
        if S<self.powers[0] or self.powers[-1]<S:
            return None
        low,high=0,self.B-1
        while low<high:
            middle=(low+high)//2
            if S<=self.powers[middle+1]:high=middle
            else:low=middle+1
        assert self.powers[low]<=S<=self.powers[low+1]
        return low


@lru_cache(None)
def word_info(w):
    state = scan(w)
    if state is None:
        return None
    lo,hi = side_interval(w)
    return float(lo),float(hi),state


def maximum(w,state):
    a,b,c,d = matrix(w)
    t = float(tail_endpoint(state,len(w)%2 == 1))
    return (a*t+b)/(c*t+d)


def core_max(a,b,center):
    core = a[::-1]+(center,)+b
    return max([0]+[d+maximum(core[:i][::-1],scan(a))+maximum(core[i+1:],scan(b))
                    for i,d in enumerate(core) if i != len(a) and d>=3])


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--table',default='avoid313_m2')
    p.add_argument('--length',type=int,default=5)
    p.add_argument('--lower',default='4.473')
    p.add_argument('--upper',default='4.52')
    p.add_argument('--backward',type=int,default=5)
    args = p.parse_args()
    table = Table(args.table)
    spec = RationalBounds([tuple(map(int,w)) for w in table.meta['language'].split(',')],
                          backward=args.backward)
    lower = Q(args.lower)
    upper = Q(args.upper)
    words = [(d,)+w for n in range(2,args.length+1)
             for d in (1,3,4) for w in product((1,2,3),repeat=n-1)
             if word_info((d,)+w) is not None]
    pool = []
    screened = 0
    for center,ad,bd in [(3,1,1),(4,3,4)]:
        aa = [w for w in words if w[0] == ad]
        bb = [w for w in words if w[0] == bd]
        for a in aa:
            la,ha,_ = word_info(a)
            for b in bb:
                if ad == bd and b<a:
                    continue
                lb,hb,_ = word_info(b)
                hi = min(center+ha+hb,float(upper))
                lo = max(center+la+lb,float(lower))
                if lo>=hi:
                    continue
                cm = core_max(a,b,center)
                if cm>=hi:
                    continue
                screened += 1
                for row in table.rows(a,b):
                    l,h = (center+E(tuple(v)) for v in row['interval'])
                    if max(float(l),cm,float(lower))<min(float(h),float(upper)):
                        pool.append(dict(row,center=center,screen_theta=cm))
    print('SCREENED',screened,'BANDS',len(pool),flush=True)
    # Prefer wide candidates; only root tuples contributing new coverage need
    # the more expensive all-position calculation.
    pool.sort(key=lambda r:float(E(tuple(r['interval'][1]))-E(tuple(r['interval'][0]))),reverse=True)
    covered = []
    accepted = []
    spectral = {}
    for row in pool:
        lo,hi = (row['center']+E(tuple(v)) for v in row['interval'])
        lo,hi = max(lo,E.cast(lower)),min(hi,E.cast(upper))
        if any(l<=lo and hi<=h for l,h in covered):
            continue
        key = row['a'],row['b'],row['center']
        if key not in spectral:
            spectral[key] = spec.root(tuple(map(int,key[0])),tuple(map(int,key[1])),key[2])
        theta = Q(spectral[key]['theta'])
        lo = max(lo,E.cast(theta))
        if lo>=hi or any(l<=lo and hi<=h for l,h in covered):
            continue
        row = {k:v for k,v in row.items() if k!='screen_theta'}
        row.update(theta=str(theta),covered_interval=[lo.data(),hi.data()])
        accepted.append(row)
        covered = union(covered+[(lo,hi)])
        print('ACCEPT',key,float(lo),float(hi),flush=True)
    output = dict(schema='berstein_language_interval_candidates_v1',table=args.table,
                  search_length=args.length,screened=screened,candidate_bands=len(pool),
                  target_window=[str(lower),str(upper)],backward_window=args.backward,
                  rows=accepted,spectral_reports=[dict(a=k[0],b=k[1],center=k[2],**v)
                                                for k,v in spectral.items()],
                  components=[[x.data() for x in iv] for iv in covered],
                  components_decimal=[[float(x) for x in iv] for iv in covered],
                  scope='Exact fixed root candidates; replay the closed table before claiming inclusion.')
    (BASE/'data'/f'{args.table}_candidates.json').write_text(json.dumps(output,indent=2)+'\n')
    print('COMPONENTS',output['components_decimal'],flush=True)


if __name__ == '__main__':
    main()
