"""Exact finite obligations for the complete Freiman Hall-ray proof.

Local endpoint conditions, general-table entry bands, all noncentral positions,
and the finite and translation chains are checked here. Infinite iteration and
Lagrange gluing are proved in ../doc/lemma2_schecker.tex. A closed general table alone does not
establish the ray. No historical success flags or archive modules are imported.
"""
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path

from prepare import (K, E, CF, matrix, cf, tail_endpoint, interval, parameters,
                     union, DIGITS, STATES, step, scan, anchor, derivative_fraction,
                     child_box, suffix_range, contains, side_pairs, channels,
                     delta_range)

A = (3, 2, 1, 1, 3)
B = (4, 3, 2, 2)
U = (1, 3, 1, 2, 1, 3)
V = (3, 1, 3, 1, 2, 1)
r0, s0, rho0 = parameters(A, B)
z0 = (1 + r0 * anchor(A)) / (1 + s0 * anchor(B))
S0 = rho0 * z0 * z0
P, H = Q(17, 100), Q(19, 100)
LOOP = (3, 3)
LEFT, RIGHT = (1, 3, 3), (3, 3)


class Kernel:
    """Interpret a fixed table; closure is established by verify.py each run."""
    def __init__(self, directory):
        self.meta = json.loads((directory / 'graph_wide.meta.json').read_text())
        m = self.meta
        assert m['coordinate'] == 'lower_endpoint_derivative_ratio'
        self.ids = {(q,p,tuple(s)): i for i,(q,p,s) in enumerate(m['side_keys'])}
        self.sides = len(self.ids)
        self.bins = m['high'] - m['low'] + 1
        self.base = Q(m['base'])
        self.low, self.high = m['low'], m['high']
        self.memory = m['memory']
        self.types = m['types']
        self.T = len(self.types)
        self.alive = (directory / 'graph_wide.alive.bin').read_bytes()
        assert len(self.alive) == self.sides**2 * self.bins * self.T
        assert all(v in (0,1) for v in self.alive) and any(self.alive)
        self.bands = [(t, *map(Q, band)) for t,band in enumerate(m['bands'])]

    def adopted(self, index):
        assert 0 <= index < len(self.alive)
        return bool(self.alive[index])

    def index(self,S):
        lo,hi=self.low-1,self.high+2
        while lo+1<hi:
            mid=(lo+hi)//2
            if self.base**mid<=S:lo=mid
            else:hi=mid
        return lo


    def side(self,word,u,bounds):
        if scan(word+u) is None:return None
        key=(len(scan(word+u)),len(word+u)%2,(word+u)[-self.memory:])
        i=self.ids[key];newrb=child_box((bounds,(Q(0),Q(0)),(Q(1),Q(1))),u,())[0]
        proto=tuple(self.meta['prototypes'][i]);length=max(self.memory,key[0])
        if self.meta.get('prehistory_interval',['0','1'])==['0','1']:
            destination=suffix_range(proto,length)
        else:
            aa,bb,cc,dd=matrix(tuple(reversed(proto[-length:])))
            destination=tuple(sorted((aa*t+bb)/(cc*t+dd) for t in map(Q,self.meta['prehistory_interval'])))
        assert contains((destination,),(newrb,))
        return {'id':i,'r':newrb,'growth':derivative_fraction(word,u,bounds)}



# Uniform comparisons and connected covers

def band(kind):
    if not kind.startswith('band_'):return None
    _,a,b=kind.split('_');return Q(a),Q(b)


@lru_cache(None)
def expressions(a,b,u,w,kind):
    def side(word,ext,lang):
        return side_pairs(scan(word),len(word)%2,ext,lang)
    cut=band(kind)
    if cut is not None:
        alpha,beta=cut;aa=side(a,u,'base');bb=side(b,w,'base')
        mix=lambda ends,t:((1-t,ends[0]),(t,ends[1]))
        return (((mix(aa,alpha),mix(bb,alpha)),(mix(aa,1-beta),mix(bb,1-beta))),)
    result=[]
    for la,lb in channels(kind):
        aa=side(a,u,la);bb=side(b,w,lb)
        result.append(((((Q(1),aa[0]),),((Q(1),bb[0]),)),
                       (((Q(1),aa[1]),),((Q(1),bb[1]),))))
    return tuple(result)


@lru_cache(maxsize=100000)
def expression_range(anchor,x,y,bounds,parity):
    coeff={}
    for c,z in x:coeff[z]=coeff.get(z,Q(0))+c
    for c,z in y:coeff[z]=coeff.get(z,Q(0))-c
    assert sum(coeff.values())==0
    positive=[[c,z] for z,c in coeff.items() if c>0]
    negative=[[-c,z] for z,c in coeff.items() if c<0]
    lo=hi=E.cast(0);i=j=0
    while i<len(positive) and j<len(negative):
        mass=min(positive[i][0],negative[j][0])
        ll,hh=delta_range(anchor,positive[i][1],negative[j][1],bounds)
        if parity:ll,hh=-hh,-ll
        lo+=mass*ll;hi+=mass*hh
        positive[i][0]-=mass;negative[j][0]-=mass
        if not positive[i][0]:i+=1
        if not negative[j][0]:j+=1
    assert i==len(positive) and j==len(negative)
    return lo,hi




class AnchorUniform:
    def __init__(self,a,b,kind,box):
        self.a=a;self.b=b;self.kind=kind;self.box=box
        self.parent=expressions(a,b,(),(),kind);self.cache={};self.checks=0

    def get(self,v):return expressions(self.a,self.b,*v)

    def ge(self,x,y):
        key=x,y
        if key not in self.cache:
            self.checks+=1
            aa=expression_range(anchor(self.a),x[0],y[0],self.box[0],len(self.a)%2)
            bb=expression_range(anchor(self.b),x[1],y[1],self.box[1],len(self.b)%2)
            self.cache[key]=(aa[0]+min(S*v for S in self.box[2] for v in bb))>=0
        return self.cache[key]

    def left_anchor(self,v):
        child=self.get(v)
        return all(any(self.ge(p[0],c[0]) for c in child) for p in self.parent)

    def right_anchor(self,v):
        child=self.get(v)
        return all(any(self.ge(c[1],p[1]) for c in child) for p in self.parent)

    def overlap(self,u,v):
        aa,bb=self.get(u),self.get(v)
        return (any(self.ge(x[1],y[0]) for x in aa for y in bb)
                and any(self.ge(y[1],x[0]) for x in aa for y in bb))

    def verify(self,menu):
        return (bool(menu) and any(self.left_anchor(v) for v in menu)
                and any(self.right_anchor(v) for v in menu)
                and all(self.overlap(u,v) for u,v in zip(menu,menu[1:])))



def certify_menu(kernel, a, b, box, target, rows, special_check):
    menu = []
    result = []
    destinations = 0
    for original in rows:
        row = dict(original)
        u, w = tuple(row['u']), tuple(row['w'])
        assert all(d in (1, 2, 3) for d in u + w)
        assert scan(a + u) is not None and scan(b + w) is not None
        l, h = map(Q, row['band'])
        assert 0 <= l <= h <= 1
        menu.append((u, w, f'band_{l}_{1-h}'))
        if row['destination'] != 'kernel':
            assert len(u) + len(w) > 0
            special_check(row)
        else:
            x, y = kernel.side(a, u, box[0]), kernel.side(b, w, box[1])
            assert x is not None and y is not None
            image = box[2][0] * y['growth'][0] / x['growth'][1], box[2][1] * y['growth'][1] / x['growth'][0]
            assert kernel.base ** kernel.low <= image[0] <= image[1] <= kernel.base ** (kernel.high + 1)
            low, high = kernel.index(image[0]), kernel.index(image[1])
            if image[1] == kernel.base ** high:
                high -= 1
            high = max(low, high)
            geometry = x['id'] * kernel.sides + y['id']
            available = []
            for t, p, q in kernel.bands:
                if all(kernel.adopted((geometry * kernel.bins + i - kernel.low) * kernel.T + t)
                       for i in range(low, high + 1)):
                    available.append((p, q, t))
            joined = []
            for p, q, t in sorted(available):
                if joined and p <= joined[-1][1]:
                    joined[-1][1] = max(joined[-1][1], q)
                    joined[-1][2].append(t)
                else:
                    joined.append([p, q, [t]])
            supporting = [component for component in joined if component[0] <= l <= h <= component[1]]
            assert supporting, ('missing_kernel_band', u, w, l, h, low, high)
            types = supporting[0][2]
            destinations += len(types) * (high - low + 1)
            row.update(geometry=geometry, bins=[low, high], types=types)
        result.append(row)
    proof = AnchorUniform(a, b, f'band_{target[0]}_{1-target[1]}', box)
    assert proof.verify(menu), 'uniform_cover_failed'
    return result, {'kernel_memberships': destinations, 'uniform_comparisons': proof.checks}

# Four local endpoint conditions

def zeta_enclosure():
    scale = 10 ** 40
    z = isqrt(13 * scale * scale)
    low, high = (Q(z, scale) - 3) / 2, (Q(z + 1, scale) - 3) / 2
    assert 0 < low <= high
    assert low * low + 3 * low - 1 <= 0 <= high * high + 3 * high - 1
    return low, high


def convert_scale(a, b, box, to_zeta):
    """Enclose S <-> V_zeta for independent r,s,scale intervals.

    With x=anchor(a),y=anchor(b),
      V_zeta = S ((1+r*zeta)/(1+r*x))^2
                   ((1+s*y)/(1+s*zeta))^2.
    Each positive unsquared factor is fractional linear in each coordinate
    separately, so its extrema lie at corners.  Rational bounds for zeta
    avoid changing the exact endpoint field used by the existing verifier.
    """
    x, y = anchor(a), anchor(b)
    values = []
    for r, s, z, scale in product(box[0], box[1], zeta_enclosure(), box[2]):
        factor = (1 + r * z) / (1 + r * x) * (1 + s * y) / (1 + s * z)
        assert factor > 0
        if not to_zeta:
            factor = 1 / factor
        values.append(scale * factor * factor)
    return min(values), max(values)


def induced_anchor_box(a, b, local):
    return local[:2] + (convert_scale(a, b, local, False),)


def signature_ok(a, b):
    return (scan(a) == scan(b) == (3,)
            and len(a) % 2 == 1 and len(b) % 2 == 0
            and a[-2:] == b[-2:] == LOOP)


def verify_local_return(local):
    assert signature_ok(LEFT, RIGHT)
    assert signature_ok(LEFT + LOOP, RIGHT + LOOP)
    assert matrix(LOOP) == (1, 3, 3, 10)
    # T_33(r)=(3+r)/(10+3r) is increasing.  Check both extrema.
    for low, high in local[:2]:
        f = lambda r: (3 + r) / (10 + 3 * r)
        assert low <= f(low) <= f(high) <= high
        # For continued fractions with digits in {1,2,3}, these bounds also
        # force the last two digits to be 33; this suffix need not be an
        # additional mathematical admissibility condition.
        assert Q(1, 4) < low <= high < Q(1, 3)
        assert Q(1, 4) < 1 / high - 3 <= 1 / low - 3 < Q(1, 3)
    # F_33(zeta)-zeta has numerator -3(zeta^2+3*zeta-1)=0.
    # Chain rule therefore multiplies both derivatives by |F_33'(zeta)|,
    # preserving V_zeta exactly; its interval is unchanged.
    assert local[2][0] > 0


def verify_entry(a, b, box, row, local):
    u, w = tuple(row['u']), tuple(row['w'])
    assert tuple(map(Q, row['band'])) == (P, H)
    assert signature_ok(a + u, b + w)
    rr, ss, _ = child_box(box, u, w)
    fa, fb = derivative_fraction(a, u, box[0]), derivative_fraction(b, w, box[1])
    scale = (box[2][0] * fb[0] / fa[1], box[2][1] * fb[1] / fa[0])
    vbox = convert_scale(a + u, b + w, (rr, ss, scale), True)
    assert contains(local, (rr, ss, vbox)), ('entry_outside_local_row', row)
    return {'u': list(u), 'w': list(w),
            'enclosure': [[str(x) for x in pair] for pair in (rr, ss, vbox)]}


def read_box(row):
    return tuple(tuple(map(Q, pair)) for pair in row['box'])


def signature(word, state, parity, suffix):
    assert scan(word) == tuple(state)
    assert len(word) % 2 == parity
    assert word[-len(suffix):] == tuple(suffix)


def verify_local_conditions(kernel, conditions):
    assert set(conditions) == {'entry', 'period', 'three_a', 'three_b'}
    prototypes = {'entry': (A, B), 'period': (A+U, B+V),
                  'three_a': (LEFT, RIGHT), 'three_b': (LEFT, RIGHT)}
    boxes = {name: read_box(row) for name, row in conditions.items()}
    reports, negative = [], []
    gamma = E.quad(3697, -172, 462)
    assert 0 < gamma < 1
    for name, row in conditions.items():
        a, b = prototypes[name]
        signature(a, row['left_state'], row['left_parity'], row['left_suffix'])
        signature(b, row['right_state'], row['right_parity'], row['right_suffix'])
        target = tuple(map(Q, row['band']))
        box = boxes[name]
        assert all(0 < lo <= hi for lo, hi in box)
        if name in ('three_a', 'three_b'):
            assert row['coordinate'] == 'V' and target == (Q(17,100), Q(19,100))
            verify_local_return(box)
            enclosing_box = induced_anchor_box(a, b, box)
        else:
            assert row['coordinate'] == 'S' and target == (Q(0), Q(1,8))
            enclosing_box = box

        def local_destination(child):
            u, w = tuple(child['u']), tuple(child['w'])
            band = tuple(map(Q, child['band']))
            destination = child['destination']
            assert destination in conditions
            if destination == 'period':
                assert name in ('entry', 'period') and u == U and w == V
                assert band == (Q(0), Q(1,8))
                assert cf(U, anchor(a+U)) == anchor(a)
                assert cf(V, anchor(b+V)) == anchor(b)
                assert derivative_fraction(a, U, box[0]) == (gamma, gamma)
                assert derivative_fraction(b, V, box[1]) == (gamma, gamma)
                rr, ss, _ = child_box(box, U, V)
                # The common derivative multiplier cancels identically.
                assert contains(boxes['period'], (rr, ss, box[2]))
            elif name in ('entry', 'period'):
                assert destination == ('three_a' if name == 'entry' else 'three_b')
                verify_entry(a, b, box, child, boxes[destination])
            else:
                assert destination == name and u == w == (3,3)
                assert band == target
                verify_local_return(box)
            dest = conditions[destination]
            signature(a+u, dest['left_state'], dest['left_parity'], dest['left_suffix'])
            signature(b+w, dest['right_state'], dest['right_parity'], dest['right_suffix'])

        translated = [dict(child, destination=('kernel' if child['destination'] == 'general'
                                              else child['destination']))
                      for child in row['menu']]
        verified, statistics = certify_menu(kernel, a, b, enclosing_box,
                                              target, translated, local_destination)
        reports.append({'condition': name, 'menu_size': len(verified),
                        'coordinate': row['coordinate'], 'box': row['box'],
                        **statistics})
        if name in ('entry', 'period', 'three_b'):
            proof = AnchorUniform(a, b, f'band_{target[0]}_{1-target[1]}', enclosing_box)
            destinations = {'period'} if name == 'entry' else (
                {'period', 'three_b'} if name == 'period' else {'three_b'})
            for destination in destinations:
                damaged = [(tuple(v['u']), tuple(v['w']),
                            f'band_{Q(v["band"][0])}_{1-Q(v["band"][1])}')
                           for v in row['menu'] if v['destination'] != destination]
                assert not proof.verify(damaged)
                negative.append({'condition': name, 'removed': destination, 'rejected': True})
    assert contains(boxes['entry'], ((r0,r0), (s0,s0), (S0,S0)))
    return reports, negative


def verify_entrances(data, kernel):
    results, children = [], 0
    for row in data:
        a, b = (tuple(map(int, row[k])) for k in ('a', 'b'))
        assert scan(a) is not None and scan(b) is not None
        assert all(1 <= d <= 4 for d in a+b)
        p, q = map(Q, row['band'])
        assert 0 <= p < q <= 1
        low, high = interval(a,b)
        parent = low+p*(high-low), low+q*(high-low)
        assert [v.data() for v in parent] == row['interval']
        covered = []
        for child in row['menu']:
            u, w = tuple(child['u']), tuple(child['w'])
            assert u or w
            assert all(d in (1,2,3) for d in u+w)
            assert tuple(map(int, child['a'])) == a+u
            assert tuple(map(int, child['b'])) == b+w
            assert child['proofs'] and all(v['kernel'] == 'graph_wide' for v in child['proofs'])
            covered.append(check_row(child, {'graph_wide': kernel}))
            children += 1
        assert any(low <= parent[0] and parent[1] <= high for low, high in union(covered))
        results.append(parent)
    return results, children

# Root membership and continuous chains

def check_row(row,kernels):
    a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
    assert a and b and all(1<=d<=4 for d in a+b)
    assert scan(a) is not None and scan(b) is not None
    p,q=map(Q,row['band']);assert 0<=p<q<=1
    r,s,rho=parameters(a,b)
    # Compute the automaton state again directly from the suffix.
    states=[max((t for t in STATES if not t or w[-len(t):]==t),key=len) for w in (a,b)]
    assert states==[scan(a),scan(b)]
    xa,xb=[tail_endpoint(t,len(w)%2==0) for t,w in zip(states,(a,b))]
    z=(1+r*xa)/(1+s*xb);S=rho*z*z
    certified=[]
    for proof in row['proofs']:
        kernel=kernels[proof['kernel']]
        ids=[]
        for w,t,ratio in zip((a,b),states,(r,s)):
            key=len(t),len(w)%2,w[-kernel.memory:];sid=kernel.ids[key];ids.append(sid)
            proto=tuple(kernel.meta['prototypes'][sid]);length=max(kernel.memory,len(t))
            aa,bb,cc,dd=matrix(tuple(reversed(proto[-length:])))
            bounds=sorted((aa*x+bb)/(cc*x+dd) for x in
                          map(Q,kernel.meta.get('prehistory_interval',['0','1'])))
            assert bounds[0]<=ratio<=bounds[1]
            # Current suffix determines every next allowed digit and state.
            assert all(step(t,d)==step(scan(proto),d) for d in (1,2,3))
        ia,ib=ids
        geom=ia*kernel.sides+ib;i=proof['bin'];typ=proof['type']
        assert geom==proof['geometry'] and kernel.low<=i<=kernel.high
        assert kernel.base**i<=S<=kernel.base**(i+1)
        assert kernel.adopted((geom*kernel.bins+i-kernel.low)*kernel.T+typ)
        expected=next((l,h) for t,l,h in kernel.bands if t==typ)
        assert tuple(map(Q,proof['band']))==expected
        certified.append(expected)
    merged=union(certified)
    assert any(l<=p and q<=h for l,h in merged)
    sides=[sorted(cf(w,tail_endpoint(t,m)) for m in (True,False)) for w,t in zip((a,b),states)]
    L,H=(sides[0][i]+sides[1][i] for i in (0,1))
    result=L+p*(H-L),L+q*(H-L)
    assert [v.data() for v in result]==row['interval']
    return result


def reaches(intervals,start,target):
    current=start
    for lo,hi in intervals:
        if lo>current or hi<=current:return False
        current=hi
    return current>=target

# Bounds at every noncentral position

def maximize(prefix, tail_state):
    return cf(prefix, tail_endpoint(tail_state, len(prefix) % 2 == 1))


@lru_cache(None)
def bulk_maximum():
    # Every global 31313-free bilateral sequence has one of these 5-letter
    # windows. Once that window is fixed, its left/right continuations are
    # independent: a 5-letter forbidden word cannot touch both new tails.
    candidates = []
    for w in product(DIGITS, repeat=5):
        if scan(w) is None:
            continue
        value = (w[2] + maximize(tuple(reversed(w[:2])), scan(tuple(reversed(w))))
                 + maximize(w[3:], scan(w)))
        candidates.append((value, w))
    return max(candidates)


def fibonacci(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def tail_radius(threshold):
    bulk, _ = bulk_maximum()
    for radius in range(4, 101):
        bound = bulk + K(Q(1, fibonacci(radius + 1)**2))
        if bound <= threshold:
            return radius, bound
    raise ValueError('No tail cutoff below the threshold; use a different target')


def bound_root(a, b, center=4, threshold=CF):
    sa, sb = scan(a), scan(b)
    if sa is None or sb is None:
        raise ValueError('Forbidden prefix')
    radius, far = tail_radius(threshold)
    core = tuple(reversed(a)) + (center,) + b
    candidates = []
    for index, digit in enumerate(core):
        if index == len(a):
            continue
        left = tuple(reversed(core[:index]))
        right = core[index+1:]
        value = digit + maximize(left, sa) + maximize(right, sb)
        candidates.append((value, {'position': index-len(a), 'type': 'core'}))
    checked = 0
    for side, near, other in [('right', b, a), ('left', a, b)]:
        # Reflecting around the origin preserves 31313 and local values.
        frontier = [((), scan(near))]
        for distance in range(1, radius + 1):
            nxt = []
            for ext, state in frontier:
                for digit in DIGITS:
                    child = step(state, digit)
                    if child is None:
                        continue
                    word = ext + (digit,)
                    nxt.append((word, child))
                    checked += 1
                    if digit <= 2:
                        # Every [0;positive digits] is <1, hence value <4.
                        continue
                    backward = tuple(reversed(near + ext)) + (center,) + other
                    # If the first digit is >=2, this local value is <4.5.
                    # Use this shortcut only because our threshold is >4.5.
                    if threshold > K(Q(9,2)) and backward[0] >= 2:
                        continue
                    value = digit + maximize(backward, scan(other)) + tail_endpoint(child, False)
                    candidates.append((value, {'side': side, 'distance': distance,
                                                'extension': ''.join(map(str, word)),
                                                'type': 'near_tail'}))
            frontier = nxt
    # The shortcut bounds are included, even when non-sharp.
    candidates.extend([(K(4), {'type': 'digits_1_2'}),
                       (K(Q(9,2)), {'type': 'backward_first_digit_ge_2'}),
                       (far, {'type': 'far_tail', 'radius': radius})])
    theta, witness = max(candidates, key=lambda entry: entry[0])
    hull = interval(a, b)
    lower, upper = max(center + hull[0], theta), center + hull[1]
    return {
        'a': ''.join(map(str,a)), 'b': ''.join(map(str,b)), 'center': center,
        'scope': 'Spectral domination only; filling still requires a closed Lem2 certificate.',
        'bulk_max': bulk_maximum()[0].data(), 'bulk_max_decimal': float(bulk_maximum()[0]),
        'bulk_window': bulk_maximum()[1],
        'radius': radius, 'enumerated_tail_prefixes': checked,
        'theta_upper': theta.data(), 'theta_upper_decimal': float(theta),
        'maximizing_bound': witness, 'theta_le_cF': theta <= CF,
        'hull': [x.data() for x in hull],
        'conditional_markov_interval': [lower.data(), upper.data()] if lower <= upper else None,
        'conditional_markov_interval_decimal': [float(lower), float(upper)] if lower <= upper else None,
        'core_bounds': [{'position': w['position'], 'upper': x.data(), 'decimal': float(x)}
                        for x,w in candidates if w['type']=='core'],
    }

# Complete ray inclusion

def verify_ray(directory, table_rows):
    kernel = Kernel(directory)
    data = json.loads((directory/'ray.json').read_text())
    assert data['schema'] == 'freiman_unified_local_admissibility_v1'
    assert data['kernel'] == 'graph_wide'
    conditions = {row['name']: row for row in data['local_conditions']}
    local, negative = verify_local_conditions(kernel, conditions)
    entrances, children = verify_entrances(data['initial_entrances'], kernel)
    direct = uses = 0
    def admit(row):
        nonlocal direct, uses
        if 'entrance' in row:
            n = row['entrance']
            entry = data['initial_entrances'][n]
            assert all(row[k] == entry[k] for k in ('a','b','band','interval'))
            result = entrances[n]
            uses += 1
        else:
            assert row['proofs'] and all(v['kernel'] == 'graph_wide' for v in row['proofs'])
            result = check_row(row, {'graph_wide': kernel})
            direct += 1
        assert [v.data() for v in result] == row['interval']
        return result
    low, high = (K(*v) for v in data['endpoint_interval'])
    l0, h0 = interval(A,B)
    assert low == CF == 4+l0 and high == CF+(h0-l0)/8
    assert K(*bound_root(A,B,4)['theta_upper']) < CF
    finite, spectral = [(low,high)], {}
    for row in data['finite_chain']:
        l,h = admit(row)
        key = row['a'], row['b'], row['center']
        assert key[2] in (3,4,5)
        if key not in spectral:
            spectral[key] = K(*bound_root(tuple(map(int,key[0])),
                                          tuple(map(int,key[1])),key[2])['theta_upper'])
        assert spectral[key].data() == row['theta_upper']
        covered = max(l+key[2],spectral[key]), h+key[2]
        assert [v.data() for v in covered] == row['covered_interval']
        finite.append(covered)
    assert reaches(finite,CF,K(Q(13,2)))
    translated = [admit(row) for row in data['translation_chain']]
    assert data['translation_target'] == ['1/2','3/2']
    assert data['translation_centers'] == 'all integers >= 6'
    assert reaches(translated,K(Q(1,2)),K(Q(3,2)))
    bulk,_ = bulk_maximum()
    assert bulk < CF
    assert not reaches(finite[1:],CF,K(Q(13,2)))
    assert not reaches(finite[:-1],CF,K(Q(13,2)))
    assert not reaches(translated[:-1],K(Q(1,2)),K(Q(3,2)))
    report = {'passed': True, 'claim': '[c_F,infinity) is contained in M and L',
              'proof_kind': 'Exact finite verification plus nested-cylinder iteration and gluing.',
              'general_kernels': 1, 'general_kernel': 'graph_wide',
              'general_kernel_states': table_rows,
              'graph_m2_data_used': False, 'ancestor_or_repetition_counter_used': False,
              'exact_endpoint_scale_equality_required': False,
              'local_conditions': local, 'local_menu_count': sum(r['menu_size'] for r in local),
              'initial_entrances': len(entrances), 'entrance_child_bands': children,
              'direct_initial_rows': direct, 'initial_rows_using_entrances': uses,
              'finite_hall_rows': len(data['finite_chain']),
              'translation_hall_rows': len(data['translation_chain']),
              'finite_covered_interval_decimal': [float(CF),float(finite[-1][1])],
              'translation_ray_start': '13/2', 'spectral_roots_recomputed': len(spectral),
              'bulk_bound': bulk.data(), 'negative_local_controls': negative,
              'negative_ray_controls_passed': True,
              'freiman_ray_in_M_verified': True, 'freiman_ray_in_L_verified': True,
              'maximality_below_cF_proved_here': False}
    return report
