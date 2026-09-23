#!/usr/bin/env python3
"""Exact experiments for 31313-free tails. Python standard library only.

Words are read from the centre outwards; fixed prefixes may contain 4,
new digits are 1,2,3. All endpoint comparisons take place in Q(sqrt(462)).
This is a local obstruction/search tool, not a Hall-ray proof.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache, total_ordering
from itertools import product
from math import isqrt
import argparse
import json
from pathlib import Path


@total_ordering
@dataclass(frozen=True)
class Q:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q) else Q(x)

    def __add__(self, other):
        other = Q.coerce(other)
        return Q(self.a + other.a, self.b + other.b)
    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __sub__(self, other):
        return self + -Q.coerce(other)

    def __rsub__(self, other):
        return Q.coerce(other) - self

    def __mul__(self, other):
        other = Q.coerce(other)
        return Q(self.a * other.a + 462 * self.b * other.b,
                 self.a * other.b + self.b * other.a)
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Q.coerce(other)
        norm = other.a**2 - 462 * other.b**2
        if not norm:
            raise ZeroDivisionError
        return self * Q(other.a / norm, -other.b / norm)

    def __rtruediv__(self, other):
        return Q.coerce(other) / self

    def sign(self):
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a or (a > 0) == (b > 0):
            return (b > 0) - (b < 0)
        # Positive rational denominators can be cleared before squaring.
        # This avoids repeated Fraction normalization in exact sign tests.
        delta = (a.numerator*b.denominator)**2 - 462*(b.numerator*a.denominator)**2
        return ((a > 0) - (a < 0)) * ((delta > 0) - (delta < 0))

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __eq__(self, other):
        if not isinstance(other, (Q, int, F)):
            return NotImplemented
        other = Q.coerce(other)
        return self.a == other.a and self.b == other.b

    def __abs__(self):
        return self if self.sign() >= 0 else -self

    def decimal(self, digits=22):
        # Display only; never used in a mathematical decision.
        from decimal import Decimal, localcontext
        with localcontext() as ctx:
            ctx.prec = digits + 20
            value = (Decimal(self.a.numerator) / Decimal(self.a.denominator)
                     + Decimal(self.b.numerator) / Decimal(self.b.denominator)
                     * Decimal(462).sqrt())
            return f'{value:.{digits}f}'

    def record(self):
        return {'a': str(self.a), 'b': str(self.b), 'decimal': self.decimal()}


BAN = '31313'
STATES = ('', '3', '31', '313', '3131')


def step(state, digit):
    candidate = state + digit
    if candidate.endswith(BAN):
        return None
    return max((s for s in STATES if candidate.endswith(s)), key=len)


def state_of(word):
    if any(a not in '1234' for a in word):
        raise ValueError('prefix digits must belong to 1,2,3,4')
    state = ''
    for digit in word:
        state = step(state, digit)
        if state is None:
            raise ValueError(f'forbidden prefix {word}')
    return state


@lru_cache(None)
def matrix(word):
    a, b, c, d = 1, 0, 0, 1
    for digit in word:
        k = int(digit)
        a, b, c, d = b, a + k*b, d, c + k*d
    return a, b, c, d


def transform(word, x):
    a, b, c, d = matrix(word)
    return (a*x + b) / (c*x + d)


def periodic(period):
    a, b, c, d = matrix(period)
    disc = (d-a)**2 + 4*b*c
    square = isqrt(disc // 462)
    if 462*square*square != disc:
        raise ValueError('period endpoint outside Q(sqrt(462))')
    return Q(F(a-d, 2*c), F(square, 2*c))


@lru_cache(None)
def extreme_tail(state, maximize):
    seen, digits = {}, ''
    current = (state, maximize)
    while current not in seen:
        seen[current] = len(digits)
        s, high = current
        choices = [d for d in '123' if step(s, d) is not None]
        digit = min(choices) if high else max(choices)
        digits += digit
        current = (step(s, digit), not high)
    cut = seen[current]
    preperiod, period = digits[:cut], digits[cut:]
    value = transform(preperiod, periodic(period))
    return value, preperiod, period


@lru_cache(None)
def cylinder(word):
    state = state_of(word)
    low_tail, *_ = extreme_tail(state, bool(len(word) % 2))
    high_tail, *_ = extreme_tail(state, not bool(len(word) % 2))
    lo, hi = transform(word, low_tail), transform(word, high_tail)
    assert lo < hi
    return lo, hi


def hull(left, right):
    l, r = cylinder(left), cylinder(right)
    return l[0] + r[0], l[1] + r[1]


def merge(intervals):
    result = []
    for lo, hi in sorted(intervals):
        if result and lo <= result[-1][1]:
            result[-1] = (result[-1][0], max(hi, result[-1][1]))
        else:
            result.append((lo, hi))
    return result


@lru_cache(None)
def extensions(word, depth):
    if not depth:
        return (word,)
    return tuple(w + d for w in extensions(word, depth-1)
                 for d in '123' if step(state_of(w), d) is not None)


def outer_components(left, right, depth):
    # Every true sum lies in this finite union; gaps are rigorous exclusions.
    return merge(hull(u, v) for u in extensions(left, depth)
                 for v in extensions(right, depth))


def interval_record(interval):
    return [x.record() for x in interval]


def gaps(components):
    return [(a[1], b[0]) for a, b in zip(components, components[1:])]


def one_step_gap(left, right):
    return gaps(outer_components(left, right, 1))


def restricted_ratio(left, right):
    lo, hi = cylinder(left)
    rlo, rhi = cylinder(right)
    return (rhi-rlo)/(hi-lo)


def locally_good(left, right):
    """Deliberately insufficient candidate predicate, used to falsify induction."""
    ratio = restricted_ratio(left, right)
    return Q(F(5,17)) <= ratio <= Q(F(17,5)) and not one_step_gap(left, right)


def full_ratio_float(left, right):
    # Descriptive Schecker ratio only, deliberately not a proof predicate.
    from decimal import Decimal, localcontext
    with localcontext() as ctx:
        ctx.prec = 60
        alpha = (Decimal(21).sqrt()-3)/6
        beta = 3*alpha
        def width(word):
            _, _, c, d = matrix(word)
            return (beta-alpha)/((c*alpha+d)*(c*beta+d))
        return str(width(right)/width(left))


def full_ratio_compare(left, right, threshold):
    """Sign of the old Schecker v minus a rational threshold, exactly.

    (1+r*alpha)(1+r*beta) = A(r)+B(r)*sqrt(21).
    Its denominator is positive, so only one quadratic sign is needed.
    """
    _, _, cl, dl = matrix(left)
    _, _, cr, dr = matrix(right)
    r, s, q = F(cl,dl), F(cr,dr), F(dl*dl,dr*dr)
    def coeff(z):
        return 1-2*z+F(5,2)*z*z, F(2,3)*z-F(1,2)*z*z
    ar, br = coeff(r)
    ass, bs = coeff(s)
    a, b = q*ar-threshold*ass, q*br-threshold*bs
    if not b:
        return (a>0)-(a<0)
    if not a or (a>0)==(b>0):
        return (b>0)-(b<0)
    delta = a*a-21*b*b
    return ((a>0)-(a<0))*((delta>0)-(delta<0))


def has_cover(left, right, depth, predicate):
    """Minimum-cardinality greedy cover among the given bounded candidates.

    Proper 3-successor means digits <=3, NOT exactly three children.
    Successful output proves one finite cover, not invariant closure.
    """
    target = hull(left, right)
    candidates = []
    for total in range(1, depth+1):
        for dl in range(total+1):
            for u in extensions(left, dl):
                for v in extensions(right, total-dl):
                    if predicate(u, v):
                        candidates.append((*hull(u, v), u, v))
    candidates.sort()
    current, index, selected = target[0], 0, []
    while current < target[1]:
        best = None
        while index < len(candidates) and candidates[index][0] <= current:
            candidate = candidates[index]
            if best is None or candidate[1] > best[1]:
                best = candidate
            index += 1
        if best is None or best[1] <= current:
            return {'covered': False, 'reached': current.record(),
                    'candidate_count': len(candidates)}
        selected.append([best[2][len(left):], best[3][len(right):]])
        current = best[1]
    return {'covered': True, 'children': selected,
            'candidate_count': len(candidates)}


def root_survey(depth):
    roots = [('3','3'), ('313','312'), ('321','431'), ('313','313'),
             ('32112','4322'), ('32113','4323'), ('32113','4322')]
    answer = []
    for left, right in roots:
        answer.append({'left': left, 'right': right,
                       'central_hull': interval_record(tuple(4+x for x in hull(left,right))),
                       'v_display_only': full_ratio_float(left,right),
                       'old_v_in_5_over_17_to_17_over_5_exact':
                           full_ratio_compare(left,right,F(5,17)) >= 0 and
                           full_ratio_compare(left,right,F(17,5)) <= 0,
                       'gaps_depth': depth,
                       'gaps': [interval_record(tuple(4+x for x in gap))
                                for gap in gaps(outer_components(left,right,depth))]})
    return answer


def periodic_skeleton(depth):
    """A candidate initial family, not a verified family of filled intervals."""
    cf = Q(F(2221564096,491993569), F(283748,491993569))
    rows = []
    for n in range(4):
        left, right = '3211'+'313121'*n+'3', '4322'+'313121'*n
        lo, hi = hull(left,right)
        assert 4+lo == cf
        components = outer_components(left,right,depth)
        rows.append({'n':n, 'left':left, 'right':right,
                     'central_hull':interval_record((4+lo,4+hi)),
                     'v_display_only':full_ratio_float(left,right),
                     'outer_depth':depth, 'outer_component_count':len(components)})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--root-depth', type=int, default=4)
    args = parser.parse_args()
    if not 1 <= args.root_depth <= 4:
        parser.error('root-depth must be between 1 and 4')
    left = right = '3131'
    components = outer_components(left, right, 1)
    witness = (Q(F(52814,100000)), Q(F(52815,100000)))
    witness_gap = next((g for g in gaps(components) if g[0] <= witness[0]
                        and witness[1] <= g[1]), None)
    assert witness_gap is not None, 'requested open interval is not excluded'
    roots = root_survey(args.root_depth)
    cf = Q(F(2221564096,491993569), F(283748,491993569))
    assert 4 + hull('32113','4322')[0] == cf
    combined = merge((4+lo,4+hi) for r in roots
                     for lo,hi in outer_components(r['left'],r['right'],args.root_depth))
    # Avoid introducing sqrt(21) into this quadratic field.
    starts_at_cf = combined[0][0] == cf
    reaches_sqrt21 = combined[0][1] > 0 and combined[0][1]*combined[0][1] >= 21
    bad_left, bad_right = '321133', '43221'
    assert locally_good(bad_left,bad_right)
    bad_gaps = gaps(outer_components(bad_left,bad_right,3))
    assert bad_gaps
    result = {
        'scope': 'Exact finite local checks only; no invariant/Hall-ray proof.',
        'alphabet_for_extensions': '123', 'forbidden_word': BAN,
        'extreme_tails': {s or 'empty': {
            name: {'value': extreme_tail(s,high)[0].record(),
                   'preperiod': extreme_tail(s,high)[1],
                   'period': extreme_tail(s,high)[2]}
            for name, high in [('min',False),('max',True)]} for s in STATES},
        'counterexample': {
            'left': left, 'right': right, 'v': '1 (exact, identical prefixes)',
            'hull': interval_record(hull(left,right)),
            'depth_one_components': [interval_record(i) for i in components],
            'witness_gap': interval_record(witness_gap),
            'requested_open_interval_excluded': True},
        'seven_roots': roots,
        'seven_roots_combined_outer_components': [interval_record(i) for i in combined],
        'finite_outer_cover_contains_cF_to_sqrt21': starts_at_cf and reaches_sqrt21,
        'cF_is_exact_minimum_of_seventh_hull': True,
        'periodic_skeleton_finite_samples':periodic_skeleton(args.root_depth),
        'secondary_4_upper_bounds':[
            {'left':r['left'], 'right':r['right'],
             'bound':(4+cylinder(r['right'][1:])[1]
                      +1/(4+cylinder(r['left'])[0])).record()}
            for r in roots if r['right'].startswith('4')],
        'candidate_predicate': 'restricted width ratio in [5/17,17/5] and connected depth-one outer union; NOT an invariant',
        'local_cover_search': [
            {'left':r['left'], 'right':r['right'], 'max_total_suffix_length':3,
             'result':has_cover(r['left'],r['right'],3,locally_good)}
            for r in roots[2:] if (r['left'],r['right']) != ('313','313')],
        'candidate_predicate_counterexample': {
            'left':bad_left, 'right':bad_right,
            'restricted_ratio':restricted_ratio(bad_left,bad_right).record(),
            'v_display_only':full_ratio_float(bad_left,bad_right),
            'satisfies_candidate_predicate': True,
            'depth_three_gaps': [interval_record(g) for g in bad_gaps],
            'bounded_successor_search':has_cover(bad_left,bad_right,3,locally_good)},
    }
    rendered = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
