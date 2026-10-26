"""Exact upper bounds on EVERY noncentral local value of a root.

Fixed digits may contain 4. The outward half words, including their prefixes,
avoid 31313; added digits are 1,2,3. The core need not globally avoid 31313.
"""
import argparse
import json
from functools import lru_cache
from itertools import product
from fractions import Fraction as Q
from pathlib import Path
from layout import DATA
from exact_cf import K, CF, cf, tail_endpoint, interval
from obstruction_probe import scan, step, DIGITS


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


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--left', default='32113')
    parser.add_argument('--right', default='4322')
    parser.add_argument('--center', type=int, default=4)
    parser.add_argument('--output', default='spectral_I7.json')
    args=parser.parse_args()
    result=bound_root(tuple(map(int,args.left)),tuple(map(int,args.right)),args.center)
    out=DATA/args.output
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
