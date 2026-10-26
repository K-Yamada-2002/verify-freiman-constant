"""Independent rational outer-cover audit; no imports from old Freiman work.

Digits appended are 1,2,3; the whole outward word avoids 31313.
This proves exclusions only, never interval filling or recursive admissibility.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
from layout import DATA

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


def cf(word, tail):
    for digit in reversed(word):
        tail = 1 / (digit + tail)
    return tail


@lru_cache(None)
def endpoint(word, minimize):
    state = scan(word)
    if state is None:
        raise ValueError('Forbidden prefix')
    pre, period = extremal_tail(state, minimize == (len(word) % 2 == 0))
    tail_digits = pre + (period * (160 // len(period) + 1))[:160]
    values = [cf(word + tail_digits, t) for t in (Q(0), Q(1))]
    return min(values), max(values)


def side_outer(word):
    return endpoint(word, True)[0], endpoint(word, False)[1]


def sum_outer(a, b):
    la, ua = side_outer(a)
    lb, ub = side_outer(b)
    return la + lb, ua + ub


def merge(intervals):
    merged = []
    for lo, hi in sorted(intervals):
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    return merged


def descendants(word, depth):
    return [word + ext for ext in product(DIGITS, repeat=depth)
            if scan(word + ext) is not None]


def rational_pair(interval):
    return [str(t) for t in interval]


def display_pair(interval):
    return [float(t) for t in interval]


def audit(a, b, depth):
    left, right = descendants(a, depth), descendants(b, depth)
    cover = merge(sum_outer(x, y) for x in left for y in right)
    gaps = [(x[1], y[0]) for x, y in zip(cover, cover[1:])]
    return {
        'left': ''.join(map(str, a)), 'right': ''.join(map(str, b)),
        'depth_each_side': depth, 'rectangle_count': len(left) * len(right),
        'parent_outer_decimal': display_pair(sum_outer(a, b)),
        'outer_component_count': len(cover),
        'certified_gaps_decimal': [display_pair(g) for g in gaps],
        'certified_gaps_rational': [rational_pair(g) for g in gaps],
    }


def main():
    base = (3, 1, 3, 1)
    # Verify the entire closed rational test interval, stronger than an open gap.
    target = (Q('0.52814'), Q('0.52815'))
    children = [(u, v, sum_outer(base + (u,), base + (v,)))
                for u, v in product((1, 2), repeat=2)]
    assert all(hi < target[0] or target[1] < lo for _, _, (lo, hi) in children)
    assert endpoint(base, True)[1] * 2 < target[0]
    assert target[1] < endpoint(base, False)[0] * 2
    reports = [audit(a, b, d) for a, b in [
        (base, base), ((3,), (3,)), ((3, 2, 1, 1, 3), (4, 3, 2, 2))]
        for d in (1, 2, 3, 4)]
    # For equal prefix 3131, two first-digit branches [a,b] and [c,d].
    # At equal Möbius distortion and scale lambda >= 1, the 22-to-12 gap
    # persists for lambda < (c-b)/(b-a). Compute a rigorous lower bound.
    a = endpoint(base + (2,), True)
    b = endpoint(base + (2,), False)
    c = endpoint(base + (1,), True)
    d = endpoint(base + (1,), False)
    threshold_lower = (c[0] - b[1]) / (b[1] - a[0])
    upper_branch_threshold_lower = (c[0] - b[1]) / (d[1] - c[0])
    # Sound interval-union logic, including contact and nested intervals.
    assert merge([(Q(0), Q(1)), (Q(2), Q(3))]) == [(Q(0), Q(1)), (Q(2), Q(3))]
    assert merge([(Q(0), Q(2)), (Q(1), Q(1)), (Q(2), Q(3))]) == [(Q(0), Q(3))]
    out = {
        'scope': 'Outer covers certify gaps only; no filling theorem is claimed.',
        'extremal_tail_automaton': [
            {'state': ''.join(map(str, s)),
             'min': extremal_tail(s, True), 'max': extremal_tail(s, False)}
            for s in STATES],
        'target': rational_pair(target), 'target_certified_missing': True,
        'children_of_3131_pair': [
            {'extension': [u, v], 'outer_decimal': display_pair(iv),
             'outer_rational': rational_pair(iv)} for u, v, iv in children],
        'equal_distortion_first_gap_scale_threshold_lower': str(threshold_lower),
        'equal_distortion_first_gap_scale_threshold_decimal': float(threshold_lower),
        'equal_distortion_reciprocal_threshold_decimal': float(1 / threshold_lower),
        'equal_distortion_last_gap_scale_threshold_decimal': float(upper_branch_threshold_lower),
        'audits': reports,
    }
    path = DATA / 'obstruction_report.json'
    path.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k not in (
        'audits', 'children_of_3131_pair', 'equal_distortion_first_gap_scale_threshold_lower')}, indent=2))
    for entry in reports:
        print(json.dumps({k: v for k, v in entry.items()
                          if k != 'certified_gaps_rational'}))


if __name__ == '__main__':
    main()
