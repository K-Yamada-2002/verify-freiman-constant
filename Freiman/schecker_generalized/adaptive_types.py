#!/usr/bin/env python3
"""Synthesize arbitrary endpoint types by cutting out discovered gaps.

Endpoint words are not restricted to a fixed shape bank. Discovery can use
floating point; the uniform cover replay uses exact quadratic inequalities
in the shared periodic-family parameter. Leaves remain proof obligations.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

from child_family_covers import word_pair
from explore import Q, F, matrix, state_of, extreme_tail, transform, hull
from frontier_obstructions import numeric_gap_candidates, HERE
from invariant_boxes import suffix_pairs, suffix_state, ALL_TYPE_LABELS
from uniform_initial_cover import mul


@lru_cache(None)
def tail_value(state, word, high):
    end = state_of(state+word)
    return transform(word, extreme_tail(end, high)[0])


@lru_cache(None)
def label_value(u, v, label):
    assert len(label)==4
    assert isinstance(label[0],str) and isinstance(label[2],str)
    assert all(z in '123' for z in label[0]+label[2])
    assert isinstance(label[1],bool) and isinstance(label[3],bool)
    left, right = word_pair(u, v)
    a, h, b, k = label
    pair=tail_value(state_of(left), a, h), tail_value(state_of(right), b, k)
    assert all(z>0 for z in pair)
    return pair


def full_labels(u, v):
    left, right = word_pair(u, v)
    p = (-1)**(len(left)+len(right))
    return ('', False, '', p < 0), ('', True, '', p > 0)


@lru_cache(None)
def affine_rows(u, v):
    def rows(x):
        mp = (14-x, 19, 53, 72-x)
        l = mul(mul(mul(matrix('3211'), mp), matrix('3')), matrix(u))
        r = mul(mul(matrix('4322'), mp), matrix(v))
        return l[2:], r[2:]
    a, b = rows(0), rows(1)
    answer = tuple(tuple((x, y-x) for x, y in zip(aa, bb)) for aa, bb in zip(a, b))
    for side in answer:
        for c0, c1 in side:
            assert c0 > 0 and c0+F(1,85)*c1 > 0
    return answer


def product_linear(a, b):
    return a[0]*b[0], a[0]*b[1]+a[1]*b[0], a[1]*b[1]


def quadratic_minimum(coefficients, lo=F(0), hi=F(1,85)):
    c, b, a = coefficients
    values = [c+b*x+a*x*x for x in (lo, hi)]
    if a > 0 and b+2*a*lo < 0 < b+2*a*hi:
        values.append(c-b*b/(4*a))
    return min(values)


@lru_cache(None)
def comparison_polynomial(u, v, first, second):
    x, y = label_value(u, v, first)
    xx, yy = label_value(u, v, second)
    left, right = word_pair(u, v)
    p = (-1)**(len(left)+len(right))
    (cl, dl), (cr, dr) = affine_rows(u, v)
    def denominator(c, d, z):
        return d[0]+c[0]*z, d[1]+c[1]*z
    lp = product_linear(denominator(cl, dl, x), denominator(cl, dl, xx))
    rp = product_linear(denominator(cr, dr, y), denominator(cr, dr, yy))
    return tuple((x-xx)*a+p*(y-yy)*b for a, b in zip(rp, lp))


@lru_cache(None)
def ge(u, v, first, second, regime='all'):
    """Prove F(first)>=F(second); keep the r,s,q correlation exactly."""
    assert regime in ('all', 'zero', 'positive')
    if first == second:
        return True
    x, y = label_value(u, v, first)
    xx, yy = label_value(u, v, second)
    left, right = word_pair(u, v, 0)
    p = (-1)**(len(left)+len(right))
    dx, dy = x-xx, p*(y-yy)
    # Both Mobius denominators are positive. Comparisons in which the two
    # summands have the same sign need no field division or polynomial.
    if dx >= 0 and dy >= 0:
        return True
    if dx <= 0 and dy <= 0:
        return False
    if regime in ('all', 'zero'):
        _, _, c, d = matrix(left)
        _, _, cc, dd = matrix(right)
        z = dx*(dd+cc*y)*(dd+cc*yy)+dy*(d+c*x)*(d+c*xx)
        if z < 0:
            return False
    return regime == 'zero' or quadratic_minimum(comparison_polynomial(u, v, first, second)) >= 0


@lru_cache(None)
def sample_ge(u, v, first, second, n):
    x, y = label_value(u, v, first)
    xx, yy = label_value(u, v, second)
    left, right = word_pair(u, v, n)
    _, _, c, d = matrix(left)
    _, _, cc, dd = matrix(right)
    p = (-1)**(len(left)+len(right))
    return ((x-xx)/((d+c*x)*(d+c*xx))
            +p*(y-yy)/((dd+cc*y)*(dd+cc*yy))) >= 0


@lru_cache(None)
def uniform_width_ratio(u,v,bound=21,regime='all'):
    """Prove 1/bound <= width(K(V))/width(K(U)) <= bound for the whole family."""
    assert bound>1 and regime in ('all','zero','positive')
    left,right=word_pair(u,v)
    x,xx=(extreme_tail(state_of(left),h)[0] for h in (False,True))
    y,yy=(extreme_tail(state_of(right),h)[0] for h in (False,True))
    dx,dy=xx-x,yy-y
    if regime in ('all','zero'):
        l,r=word_pair(u,v,0)
        _,_,c,d=matrix(l);_,_,cc,dd=matrix(r)
        lp=(d+c*x)*(d+c*xx);rp=(dd+cc*y)*(dd+cc*yy)
        if bound*dy*lp<dx*rp or bound*dx*rp<dy*lp:return False
    if regime=='zero':return True
    (cl,dl),(cr,dr)=affine_rows(u,v)
    def prod(c,d,a,b):
        return product_linear((d[0]+c[0]*a,d[1]+c[1]*a),
                              (d[0]+c[0]*b,d[1]+c[1]*b))
    lp,rp=prod(cl,dl,x,xx),prod(cr,dr,y,yy)
    lower=tuple(bound*dy*a-dx*b for a,b in zip(lp,rp))
    upper=tuple(bound*dx*b-dy*a for a,b in zip(lp,rp))
    return quadratic_minimum(lower)>=0 and quadratic_minimum(upper)>=0


@lru_cache(None)
def point(u, v, label, n=0):
    x, y = label_value(u, v, label)
    left, right = word_pair(u, v, n)
    _, _, c, d = matrix(left)
    _, _, cc, dd = matrix(right)
    r, s, q = c/d, cc/dd, (d/dd)**2
    x, y = float(x.decimal()), float(y.decimal())
    p = (-1)**(len(left)+len(right))
    return x/(1+r*x)+p*q*y/(1+s*y)


@lru_cache(None)
def simplify_side(state, word, high):
    value = tail_value(state, word, high)
    for length in range(len(word)+1):
        for h in (False, True):
            if tail_value(state, word[:length], h) == value:
                return word[:length], h
    raise AssertionError('the original endpoint must be a candidate')


def simplify(u, v, label):
    left, right = word_pair(u, v)
    a, h, b, k = label
    return simplify_side(state_of(left), a, h)+simplify_side(state_of(right), b, k)


def lifted(du, dv, label):
    a, h, b, k = label
    return du+a, h, dv+b, k


def gap_label(base_left, base_right, words, upper):
    a, b = words
    assert a.startswith(base_left) and b.startswith(base_right)
    return (a[len(base_left):], bool(len(a) % 2) != upper,
            b[len(base_right):], bool(len(b) % 2) != upper)


class TypeRegistry:
    def __init__(self):
        self.types = []
        self.lookup = {}

    def register(self, pair):
        direct = tuple(sorted(pair))
        reflected = tuple(sorted((z[2:]+z[:2] for z in pair)))
        key = min(direct, reflected)
        if key not in self.lookup:
            self.lookup[key] = len(self.types)
            self.types.append(key)
        return self.lookup[key], direct != key


class AdaptiveSearch:
    def __init__(self, gap_depth=4, samples=None, max_step=2, regime='all'):
        if samples is None:
            samples={'all':(0,1),'zero':(0,),'positive':(1,2)}[regime]
        self.gap_depth, self.samples, self.max_step = gap_depth, samples, max_step
        self.regime = regime
        self.registry = TypeRegistry()
        self.discoveries = []
        self.options = lru_cache(None)(self._options)
        self.rules = {}
        self.known={}
        obstruction_path=HERE/'induction_obstructions.json'
        if obstruction_path.exists():
            for row in json.loads(obstruction_path.read_text())['obstructions']:
                self.known.setdefault((row['left_suffix'],row['right_suffix']),[]).append(row)

    def ordered(self, u, v, a, b):
        if ge(u, v, b, a, self.regime):
            return a, b
        if ge(u, v, a, b, self.regime):
            return b, a
        return None

    def cut(self, u, v, components, lo, hi):
        """Conservatively retain interval pieces on either side of a cut."""
        answer = []
        for a, b in components:
            if ge(u, v, lo, b, self.regime) or ge(u, v, a, hi, self.regime):
                answer.append((a, b))
                continue
            # A boundary that crosses the old endpoint as n varies is dealt
            # with conservatively; separate parameter regimes can recover it.
            if ge(u, v, lo, a, self.regime) and ge(u, v, b, lo, self.regime) and lo != a:
                answer.append((a, lo))
            if ge(u, v, b, hi, self.regime) and ge(u, v, hi, a, self.regime) and hi != b:
                answer.append((hi, b))
        return answer

    def _options(self, u, v):
        components = [full_labels(u, v)]
        cuts = []
        for row in self.known.get((u,v),()):
            if (self.regime=='positive' and row['n']==0) or (self.regime=='zero' and row['n']!=0):
                continue
            left,right=word_pair(u,v,row['n'])
            lower,upper=row['boundary_words']
            a=simplify(u,v,gap_label(left,right,lower,True))
            b=simplify(u,v,gap_label(left,right,upper,False))
            if len(left)%2:a,b=b,a
            cuts.append((a,b,row['n']))
            components=self.cut(u,v,components,a,b)
        for n in self.samples:
            left, right = word_pair(u, v, n)
            for _, _, lower, upper in numeric_gap_candidates(left, right, self.gap_depth):
                a = simplify(u, v, gap_label(left, right, lower, True))
                b = simplify(u, v, gap_label(left, right, upper, False))
                if len(left) % 2:
                    a, b = b, a
                if (a,b,n) not in cuts:
                    cuts.append((a, b, n))
                    components = self.cut(u, v, components, a, b)
        if not cuts:
            self.registry.register(components[0])
            return tuple(components)
        # Retain the existing bank as well: a smaller old type may be uniform
        # across n even when the maximal new component changes its endpoint
        # order. New cuts augment the bank rather than replacing it.
        for pattern in ALL_TYPE_LABELS[1:]:
            try:
                a,b=(simplify(u,v,z) for z in pattern)
            except ValueError:
                continue
            pair=self.ordered(u,v,a,b)
            if pair is not None and all(sample_ge(u,v,lo,pair[1],n) or sample_ge(u,v,pair[0],hi,n)
                                        for lo,hi,n in cuts):
                components.append(pair)
        components=list(dict.fromkeys(components))
        # Label equality is stronger than value equality; remove zero pieces.
        components = [(a, b) for a, b in components
                      if not ge(u, v, a, b, self.regime)]
        for pair in components:
            self.registry.register(pair)
        if cuts:
            self.discoveries.append({'left_suffix':u, 'right_suffix':v,
                                     'cuts':cuts, 'components':components})
        return tuple(components)

    def cover(self, u, v, parent):
        left, right = word_pair(u, v)
        offers = []
        for du, dv in suffix_pairs(suffix_state(left), suffix_state(right), self.max_step):
            for pair in self.options(u+du, v+dv):
                a, b = (lifted(du, dv, z) for z in pair)
                ep = self.ordered(u, v, a, b)
                if ep is not None:
                    offers.append((point(u, v, ep[1]), du, dv, pair, ep))
        offers.sort(reverse=True)
        current, finish = parent
        chain = []
        while not ge(u, v, current, finish, self.regime):
            best = next((o for o in offers if ge(u, v, current, o[4][0], self.regime)
                         and ge(u, v, o[4][1], current, self.regime)
                         and not ge(u, v, current, o[4][1], self.regime)), None)
            if best is None:
                return None
            _, du, dv, pair, ep = best
            chain.append({'suffixes':(du,dv), 'endpoints':pair,
                          'type':self.registry.register(pair)})
            current = ep[1]
        return {'left_suffix':u, 'right_suffix':v, 'endpoints':parent,
                'type':self.registry.register(parent), 'regime':self.regime,
                'children':chain}


def verify_row(row, max_step=2):
    u, v = row['left_suffix'], row['right_suffix']
    assert all(z in '123' for z in u+v)
    regime = row['regime']
    a, b = (tuple(z) for z in row['endpoints'])
    assert ge(u,v,b,a,regime) and not ge(u,v,a,b,regime)
    current = a
    for child in row['children']:
        du, dv = child['suffixes']
        assert 1 <= len(du)+len(dv) <= max_step
        assert all(z in '123' for z in du+dv)
        l, r = word_pair(u+du, v+dv)
        state_of(l); state_of(r)
        pair = tuple(tuple(z) for z in child['endpoints'])
        assert ge(u+du,v+dv,pair[1],pair[0],regime)
        lo, hi = (lifted(du,dv,z) for z in pair)
        if not ge(u,v,hi,lo,regime):
            lo,hi = hi,lo
        assert ge(u,v,hi,lo,regime)
        assert ge(u,v,current,lo,regime)
        assert ge(u,v,hi,current,regime)
        current = hi
    assert ge(u,v,current,b,regime)


def old_type(u,v,kind):
    if kind == 0:
        return full_labels(u,v)
    a,b = (simplify(u,v,z) for z in ALL_TYPE_LABELS[kind])
    return (a,b) if ge(u,v,b,a) else (b,a)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gap-depth',type=int,default=5)
    ap.add_argument('--max-step',type=int,default=2)
    ap.add_argument('--regime',choices=('all','zero','positive'),default='all')
    ap.add_argument('--layers',type=int,default=1)
    ap.add_argument('--focus',nargs=3)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--verify',type=Path)
    args = ap.parse_args()
    if args.verify:
        data=json.loads(args.verify.read_text())
        for row in data['covers']:verify_row(row,data['max_step'])
        print('verified',len(data['covers']),'uniform local adaptive covers; leaves unproved')
        return
    search=AdaptiveSearch(args.gap_depth,max_step=args.max_step,regime=args.regime)
    initial=[('1','',0),('2','',0),('','1',4)]
    if args.focus:initial=[(args.focus[0],args.focus[1],int(args.focus[2]))]
    frontier=[(u,v,old_type(u,v,k)) for u,v,k in initial]
    roots=frontier[:];done={};failed=[]
    for layer in range(args.layers):
        new=[]
        for u,v,pair in frontier:
            key=u,v,pair
            if key in done:continue
            row=search.cover(u,v,pair)
            if row is None:
                failed.append(key);print('FAILED',u,v,flush=True);continue
            verify_row(row,args.max_step);done[key]=row
            print('covered',u or '-',v or '-', 'types',len(search.registry.types),flush=True)
            new.extend((u+c['suffixes'][0],v+c['suffixes'][1],c['endpoints']) for c in row['children'])
        frontier=list(dict.fromkeys(new))
    result={'status':'exact uniform local covers with dynamically generated types; NOT closed',
            'gap_depth':args.gap_depth,'max_step':args.max_step,'regime':args.regime,
            'samples_used_only_for_discovery':search.samples,'roots':roots,
            'types':search.registry.types,'covers':list(done.values()),
            'failed':failed,'unproved_frontier':[z for z in frontier if z not in done],
            'gap_driven_type_additions':search.discoveries}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
