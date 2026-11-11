"""Root coverage and uniform noncentral bounds for the interval proof.

Finite checks in this module discharge the hypotheses of the shrinking-cylinder,
compatible-past, and periodic-block lemmas proved in PROOF.md. The module reads
only current certificates and imports only the current exact generator.
"""
from functools import lru_cache
from itertools import product
import json

from sage.all import QQ, ZZ, fibonacci

from prepare import (select_language, suffix_state, cf_matrix, evaluate_cf,
                     continuant_parameters, oriented_tail_endpoints, cylinder_hull,
                     continuant_bounds, extremal_tail_value, periodic_tail_value,
                     parse_rational, serialize_quadratic)


class RationalBounds:
    def __init__(self, forbidden, backward=8, precision=40):
        self.forbidden = tuple(tuple(w) for w in forbidden)
        assert self.forbidden and all(w[::-1] in self.forbidden for w in self.forbidden)
        self.memory = max(map(len,self.forbidden))-1
        self.backward = backward
        self.precision = precision
        self.tail = lru_cache(None)(self._tail)

    def legal(self,w):
        return not any(w[i:i+len(b)] == b for b in self.forbidden
                       for i in range(len(w)-len(b)+1))

    def cf(self,w,x):
        return evaluate_cf(w, QQ(x))

    def _tail(self,history,minimum):
        out = ()
        for n in range(self.precision):
            choices = [d for d in (1,2,3) if self.legal(history+out+(d,))]
            # The supported forbidden words contain no 2: appending only 2
            # is always possible. Thus no greedy choice is a dead end.
            assert all(2 not in w for w in self.forbidden)
            d = max(choices) if minimum == (n%2 == 0) else min(choices)
            out += (d,)
        return tuple(sorted(self.cf(out,t) for t in (QQ(0),QQ(1))))

    def upper(self,prefix,history):
        bounds = self.tail(history[-self.memory:],len(prefix)%2 == 1)
        return self.cf(prefix,bounds[1 if len(prefix)%2 == 0 else 0])

    @lru_cache(None)
    def far(self):
        n = self.backward
        assert n >= self.memory
        values = []
        count = 0
        for past in product((1,2,3),repeat=n):
            w = past+(3,)
            if not self.legal(w):
                continue
            # Digits 1 and 2 have local value <4; digit 3 is the only case
            # needing enumeration. The past beyond this window is arbitrary.
            back = max(self.cf(past[::-1],t) for t in (QQ(0),QQ(1)))
            value = 3+back+self.upper((),w)
            values.append((value,past))
            count += 1
        bound,witness = max(values)
        return max(bound,QQ(4)),witness,count

    def root(self,a,b,center=4):
        assert self.legal(a) and self.legal(b)
        core = a[::-1]+(center,)+b
        candidates = [(self.far()[0],{'type':'far','past':self.far()[1]}),
                      (QQ(4),{'type':'digits_1_2'})]
        for i,d in enumerate(core):
            if i == len(a):
                continue
            value = d+self.upper(core[:i][::-1],a)+self.upper(core[i+1:],b)
            candidates.append((value,{'type':'core','position':i-len(a)}))
        counted = 0
        for side,near,other in [('left',a,b),('right',b,a)]:
            frontier = [()]
            # At distance >n the last n backward digits and the current
            # digit are all in the legal appended word, so far() applies.
            for distance in range(1,self.backward+1):
                children = []
                for ext in frontier:
                    for d in (1,2,3):
                        w = ext+(d,)
                        if not self.legal(near+w):
                            continue
                        children.append(w)
                        counted += 1
                        if d != 3:
                            continue
                        back = (near+ext)[::-1]+(center,)+other
                        if self.far()[0]>=QQ((9, 2)) and back[0]>=2:
                            continue  # value <3+1/2+1=4.5
                        value = d+self.upper(back,other)+self.upper((),near+w)
                        candidates.append((value,{'type':'near','side':side,
                                                 'distance':distance,'extension':w}))
                frontier = children
        theta,witness = max(candidates,key=lambda v:v[0])
        return dict(theta=str(theta),theta_decimal=float(theta),witness=witness,
                    forbidden=self.forbidden,backward=self.backward,
                    tail_precision=self.precision,far_upper=str(self.far()[0]),
                    far_witness=self.far()[1],far_windows=self.far()[2],
                    near_prefixes=counted,
                    scope='Uniform over all infinite legal tails and all noncentral positions.')


def compatible_past(a,b,center,forbidden):
    bad=tuple(tuple(w) for w in forbidden)
    assert all(w==w[::-1] and 2 not in w for w in bad)
    memory=max(map(len,bad))-1
    bounds=RationalBounds(bad,backward=memory,precision=60)
    assert bounds.legal(a) and bounds.legal(b)
    interfaces=[]
    for side,near,other in [('left',a,b),('right',b,a)]:
        prefix=near[::-1]+(center,)+other
        terminal=bounds.tail(other[-memory:],True)[0],bounds.tail(other[-memory:],False)[1]
        past=tuple(sorted(bounds.cf(prefix,t) for t in terminal))
        checks=[]
        for first in product((1,2,3),repeat=memory):
            if not bounds.legal(near+first):continue
            low=bounds.tail(first[::-1],True)[1]
            high=bounds.tail(first[::-1],False)[0]
            assert low<=past[0]<=past[1]<=high
            checks.append(dict(first=''.join(map(str,first)),minimum_upper=str(low),maximum_lower=str(high)))
        assert checks
        interfaces.append(dict(side=side,past=[str(x) for x in past],checks=checks))
    core=a[::-1]+(center,)+b
    values=[]
    for i,d in enumerate(core):
        if i==len(a):continue
        value=d+bounds.upper(core[:i][::-1],a)+bounds.upper(core[i+1:],b)
        values.append(dict(position=i-len(a),upper=str(value)))
    return dict(a=''.join(map(str,a)),b=''.join(map(str,b)),center=center,
                passed=True,interfaces=interfaces,core_values=values,
                core_upper=str(max(parse_rational(v['upper']) for v in values)),
                scope='Appended positions compare to legal bilateral sequences; the finite core has the separately listed rational bound.')


def union(intervals):
    merged = []
    for low, high in sorted(intervals):
        assert low < high
        if merged and low <= merged[-1][1]:
            merged[-1] = merged[-1][0], max(merged[-1][1], high)
        else:
            merged.append((low, high))
    return merged


class Table:
    """Interpret a fixed, freshly replayed table at actual finite prefixes."""
    def __init__(self, data, name):
        self.meta = json.loads((data / (name + '.meta.json')).read_text())
        self.bits = (data / (name + '.alive.bin')).read_bytes()
        self.name = name
        m = self.meta
        self.field = select_language(m['language'])
        self.ids = {(q, p, tuple(w)): i for i, (q, p, w) in enumerate(m['keys'])}
        self.B = m['high'] - m['low'] + 1
        self.T = len(m['bands'])
        assert len(self.bits) == len(self.ids) ** 2 * self.B * self.T
        assert all(b in (0, 1) for b in self.bits)

    @lru_cache(None)
    def side_id(self, word):
        assert word and all(d in (1, 2, 3, 4) for d in word)
        state = suffix_state(word)
        assert state is not None
        key = len(state), len(word) % 2, word[-self.meta['memory']:]
        index = self.ids[key]
        prototype = tuple(self.meta['prototypes'][index])
        assert suffix_state(prototype) == state
        low, high = continuant_bounds(prototype, self.meta['memory'])
        _, _, p, q = cf_matrix(word)
        assert low <= QQ((p, q)) <= high
        return index

    def check_row(self, row):
        a, b = tuple(map(int, row['a'])), tuple(map(int, row['b']))
        assert row['center'] in (3, 4)
        left, right = self.side_id(a), self.side_id(b)
        geometry = left * len(self.ids) + right
        assert geometry == row['geometry']
        r, s, rho = continuant_parameters(a, b)
        ratio = (1 + r * oriented_tail_endpoints(a)[0]) / (1 + s * oriented_tail_endpoints(b)[0])
        scale = rho * ratio * ratio
        exponent = row['bin']
        base = parse_rational(self.meta['base'])
        assert self.meta['low'] <= exponent <= self.meta['high']
        assert base ** exponent <= scale <= base ** (exponent + 1)
        types = row['types']
        assert types and len(set(types)) == len(types)
        admitted = []
        for kind in types:
            assert isinstance(kind, int) and 0 <= kind < self.T
            index = ((geometry * self.B + exponent - self.meta['low']) * self.T + kind)
            assert self.bits[index] == 1
            admitted.append(tuple(map(parse_rational, self.meta['bands'][kind])))
        p, q = map(parse_rational, row['band'])
        assert 0 <= p < q <= 1
        assert any(low <= p and q <= high for low, high in union(admitted))
        aa, bb = cylinder_hull(a), cylinder_hull(b)
        low, high = aa[0] + bb[0], aa[1] + bb[1]
        return (row['center'] + low + p * (high - low),
                row['center'] + low + q * (high - low))


def bulk_and_periodic_endpoint(language, field):
    forbidden = [tuple(map(int, word)) for word in language.split(',')]
    length = max(map(len, forbidden))
    assert length == 5 and all(w == w[::-1] for w in forbidden)
    def maximum(word, state):
        return evaluate_cf(word, extremal_tail_value(state, len(word) % 2 == 1))
    values = [w[2] + maximum(w[:2][::-1], suffix_state(w[::-1])) + maximum(w[3:], suffix_state(w))
              for w in product((1, 2, 3), repeat=5) if suffix_state(w) is not None]
    coefficient, word = ((QQ((4, 19)), '313121') if language == '31313'
                         else (QQ((4, 181)), '3131213132'))
    bulk = coefficient * field.gen()
    assert max(values) == bulk
    digits = tuple(map(int, word))
    assert suffix_state(digits * 3) is not None
    periodic_values = []
    for i, d in enumerate(digits):
        left = tuple(digits[(i - j) % len(digits)] for j in range(1, len(digits) + 1))
        right = tuple(digits[(i + j) % len(digits)] for j in range(1, len(digits) + 1))
        periodic_values.append(d + periodic_tail_value(left, field) + periodic_tail_value(right, field))
    assert max(periodic_values) == bulk
    return bulk, {'word': word, 'maximum': serialize_quadratic(bulk),
                  'legal_windows': len(values), 'positions': len(digits)}


def inward(x, lower):
    """Round an algebraic endpoint inward to eight decimal places, exactly."""
    denominator = 10 ** 8
    scaled = denominator * x
    numerator = scaled.ceil() if lower else scaled.floor()
    return QQ((numerator, denominator))


def verify_group(table, rows, bulk, cap):
    """Recheck all roots, not stored numerical success flags or old logs."""
    forbidden = [tuple(map(int, w)) for w in table.meta['language'].split(',')]
    rational = RationalBounds(forbidden, backward=8)
    candidates = sorted({(r['a'], r['b'], r['center']) for r in rows},
                        key=lambda x: (len(x[0]) + len(x[1]), x))
    cache = {}
    def extension(word, prefix):
        return word.startswith(prefix) and all(d in '123' for d in word[len(prefix):])
    def bound(key):
        if key not in cache:
            a, b, center = tuple(map(int, key[0])), tuple(map(int, key[1])), key[2]
            try:
                witness = compatible_past(a, b, center, forbidden)
                theta = max(bulk, table.field(parse_rational(witness['core_upper'])))
                summary = {'method': 'compatible_past', 'core_upper': witness['core_upper'],
                           'interface_contexts': sum(len(v['checks']) for v in witness['interfaces'])}
            except AssertionError:
                witness = rational.root(a, b, center)
                theta = table.field(parse_rational(witness['theta']))
                summary = {'method': 'finite_backward_windows', 'far_windows': witness['far_windows'],
                           'near_prefixes': witness['near_prefixes'], 'rational_theta': witness['theta']}
            cache[key] = theta, summary
        return cache[key][0]
    intervals = []
    for row in rows:
        low, high = table.check_row(row)
        ancestor = next(key for key in candidates
                        if key[2] == row['center'] and extension(row['a'], key[0])
                        and extension(row['b'], key[1]))
        low, high = max(low, bound(ancestor)), min(high, table.field(cap))
        assert low < high
        intervals.append((low, high))
    components = union(intervals)
    rational_components = [(inward(low, True), inward(high, False)) for low, high in components]
    for (low, high), (a, b) in zip(components, rational_components):
        assert low <= a < b <= high
    margin = min(table.field(a) - bulk for a, _ in rational_components)
    assert margin > 0
    radius = next(r for r in range(2, 101)
                  if table.field(QQ((2, fibonacci(r + 1) ** 2))) < margin / 2)
    return {'root_bands': len(rows), 'components': [[serialize_quadratic(x) for x in pair] for pair in components],
            'rational_components': [[str(x) for x in pair] for pair in rational_components],
            'noncentral_bounds': [dict(a=k[0], b=k[1], center=k[2], theta=serialize_quadratic(v[0]), **v[1])
                                  for k, v in cache.items()],
            'gluing_margin': serialize_quadratic(margin), 'gluing_radius': radius}


def verify_intervals(data):
    """Discharge interval obligations after the caller replays both families.

    Each field is processed completely before switching languages. Only
    serialized reports and rational intervals survive the field selection.
    """
    certificate = json.loads((data / 'roots.json').read_text())
    assert certificate['schema'] == 'markov_interior_roots_v1'
    reports = {}
    for name, language, cap in [('original', '31313', parse_rational('4.52782956')),
                                ('table', '31313,13131', parse_rational('4.5252'))]:
        table = Table(data, name)
        assert table.meta['language'] == language == certificate[name]['language']
        bulk, periodic = bulk_and_periodic_endpoint(language, table.field)
        group = verify_group(table, certificate[name]['rows'], bulk, cap)
        radicand = table.meta['radicand']
        group.update(language=language, field_basis=[1, 2, radicand, 2*radicand],
                     bulk=serialize_quadratic(bulk),
                     periodic_endpoint=periodic)
        if name == 'original':
            group['paper'] = verify_group(table, certificate[name]['paper_rows'], bulk, cap)
        reports[name] = group
    # Join different quadratic fields only after inward rational rounding.
    all_intervals = union(tuple(map(QQ, pair)) for report in reports.values()
                          for pair in report['rational_components'])
    paper = [tuple(map(QQ, pair)) for pair in reports['original']['paper']['rational_components']]
    targets = [('original_paper', '4.52578', '4.52754', paper),
               ('extended_component', '4.52173315', '4.52762938', all_intervals),
               ('lower_interval', '4.51104888', '4.52', all_intervals)]
    sqrt_scale = 10 ** 40
    sqrt_lower = QQ((ZZ(462 * sqrt_scale ** 2).isqrt(), sqrt_scale))
    freiman_lower = (2221564096 + 283748 * sqrt_lower) / 491993569
    assert all(high < freiman_lower for _, high in all_intervals)
    claims = []
    for label, a, b, available in targets:
        low, high = parse_rational(a), parse_rational(b)
        assert low < high < freiman_lower
        assert any(l <= low and high <= h for l, h in available), label
        claims.append({'name': label, 'interval': [a, b], 'in_M_and_L': True,
                       'below_freiman_constant': True})
    return {'passed': True, 'claims': claims, 'tables': reports,
            'combined_rational_components': [[str(x) for x in pair] for pair in all_intervals],
            'proof_basis': 'Finite checks plus the shrinking-cylinder, compatible-past and gluing lemmas in PROOF.md',
            'whole_conjecture_proved': False, 'global_maximality_proved': False,
            'new_lean_formalization_claimed': False}
