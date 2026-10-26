"""Independent rational checks supplementing verify_hall_ray.py --full.

This imports no project arithmetic or automaton implementation. It rebuilds
extrema using literal forbidden-substring tests and backward CF evaluation.
It checks all 136 saved bands and their connections, plus the endpoint menus
at concrete representatives. The latter is an implementation cross-check,
not a replacement for the universal box proofs or the full kernel replay.
"""
from layout import artifact_path
import hashlib
import json
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path
from layout import DATA

BASE = DATA
DEPTH = 180


def evaluate(word, tail):
    for digit in reversed(word):
        tail = 1 / (int(digit) + tail)
    return tail


@lru_cache(None)
def endpoint(word, minimize):
    assert word and '31313' not in word
    extended = word
    for _ in range(DEPTH):
        allowed = [str(d) for d in (1, 2, 3) if not (extended + str(d)).endswith('31313')]
        # Odd CF digits reverse the order; even digits preserve it.
        odd = (len(extended) + 1) % 2 == 1
        extended += max(allowed) if minimize == odd else min(allowed)
    return tuple(sorted(evaluate(extended, t) for t in (Q(0), Q(1))))


def band(a, b, p, q):
    lows = tuple(x + y for x, y in zip(endpoint(a, True), endpoint(b, True)))
    highs = tuple(x + y for x, y in zip(endpoint(a, False), endpoint(b, False)))
    return tuple(tuple((1-t)*l + t*h for l, h in zip(lows, highs)) for t in (p, q))


def sign(a, b):
    """Sign of a+b*sqrt(462), using rational squares only."""
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0 or (a > 0) == (b > 0):
        return 1 if b > 0 else -1
    z = a*a - 462*b*b
    return ((z > 0) - (z < 0)) * (1 if a > 0 else -1)


def check_saved(bounds, value):
    a, b = map(Q, value)
    lo, hi = bounds
    assert sign(a-lo, b) >= 0 and sign(hi-a, -b) >= 0
    assert hi-lo < Q(1, 10**80)


def radical_bounds(value):
    a, b = map(Q, value)
    scale = 10**150
    r = isqrt(462*scale*scale)
    return tuple(sorted((a+b*Q(r, scale), a+b*Q(r+1, scale))))


def menu_check(a, b, filename, target):
    data = json.loads((BASE / filename).read_text())
    parent = band(a, b, *target)
    children = []
    for row in data['menu']:
        u, w = (''.join(map(str, row[key])) for key in ('u', 'w'))
        children.append(band(a+u, b+w, *map(Q, row['band'])))
    # Equal inherited left endpoints cannot be distinguished by rational
    # enclosures. Their symbolic identity is checked by the main verifier.
    if target[0] == 0:
        assert children[0][0][0] <= parent[0][1]
        assert parent[0][0] <= children[0][0][1]
    else:
        assert children[0][0][1] < parent[0][0]
    for left, right in zip(children, children[1:]):
        assert left[1][0] > right[0][1]
        assert right[1][0] > left[0][1]
    assert children[-1][1][0] > parent[1][1]
    return len(children)


def main():
    data = json.loads((BASE / 'hall_ray_certificate.json').read_text())
    root = band('32113', '4322', Q(0), Q(1, 8))
    for bounds, saved in zip(root, data['endpoint_interval']):
        check_saved(tuple(x+4 for x in bounds), saved)
    counts = {}
    for name in ('finite_chain', 'translation_chain'):
        edge = root[1][0]+4 if name == 'finite_chain' else Q(1, 2)
        for row in data[name]:
            raw = band(row['a'], row['b'], *map(Q, row['band']))
            for bounds, saved in zip(raw, row['interval']):
                check_saved(bounds, saved)
            center = row.get('center', 0)
            lower = raw[0][1]+center
            if 'theta_upper' in row:
                lower = max(lower, radical_bounds(row['theta_upper'])[1])
            upper = raw[1][0]+center
            assert lower < edge < upper
            edge = upper
        assert edge > (Q(13, 2) if name == 'finite_chain' else Q(3, 2))
        counts[name] = len(data[name])
    A, B, U, V = '32113', '4322', '131213', '313121'
    menus = {
        'root': menu_check(A, B, 'root_endpoint_connected.json', (Q(0), Q(1, 8))),
        'E': menu_check(A+U, B+V, 'stable_endpoint_uniform.json', (Q(0), Q(1, 8))),
        'R0': menu_check(A+'1312'+'3'*6, B+'31'+'3'*6,
                         'root_thirdigit_replayed.json', (Q(17, 100), Q(19, 100))),
        'R1': menu_check(A+U+'1312'+'3'*4, B+V+'31'+'3'*4,
                         'stable_thirdigit_replayed.json', (Q(17, 100), Q(19, 100))),
    }
    # A genuine full-hull gap must remain visible to this independent code.
    x = Q('0.52814')
    parent = band('3131', '3131', Q(0), Q(1))
    assert parent[0][1] < x < parent[1][0]
    for u in '12':
        for w in '12':
            child = band('3131'+u, '3131'+w, Q(0), Q(1))
            assert child[1][1] < x or x < child[0][0]
    sources = ['layout.py', Path(__file__).name, 'hall_ray_certificate.json',
               'root_endpoint_connected.json', 'stable_endpoint_uniform.json',
               'root_thirdigit_replayed.json', 'stable_thirdigit_replayed.json']
    report = {
        'passed': True, 'appended_digits_for_rational_enclosures': DEPTH,
        'independent_band_rows': counts, 'concrete_endpoint_menu_rows': menus,
        'strict_connections_verified': True, 'known_full_hull_gap_detected': True,
        'scope': 'Independent finite checks. Universal closure and exact endpoint inheritance require verify_hall_ray.py --full and the analytic proof.',
        'sha256': {f: hashlib.sha256(artifact_path(f).read_bytes()).hexdigest() for f in sources},
    }
    (BASE / 'schecker_proof_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
