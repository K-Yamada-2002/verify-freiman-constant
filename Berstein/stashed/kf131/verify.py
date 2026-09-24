#!/usr/bin/env python3
"""Exact obstructions and finite bundle refinements; NOT an interior proof."""
import argparse
import json
from pathlib import Path
from exact import Q, F, STATES, step, state_of, extreme_tail, cylinder, hull, merge, transform


def children(u, v):
    """Split the wider hull, keeping every legal child."""
    a, b = cylinder(u)
    c, d = cylinder(v)
    if b-a >= d-c:
        return [(u+k, v) for k in '123' if step(state_of(u), k) is not None]
    return [(u, v+k) for k in '123' if step(state_of(v), k) is not None]


def exclusion(u, v, target, budget=100000):
    """Build an exact finite exclusion tree, failing if the budget is exhausted."""
    nodes = []
    def visit(u, v):
        if len(nodes) >= budget:
            raise RuntimeError('Unresolved exclusion: node budget exhausted')
        i = len(nodes)
        node = {'u': u, 'v': v, 'children': []}
        nodes.append(node)
        lo, hi = hull(u, v)
        if hi < target[0] or target[1] < lo:
            return i
        node['children'] = [visit(a, b) for a, b in children(u, v)]
        return i
    visit(u, v)
    return nodes


def replay_exclusion(nodes, target):
    seen = set()
    def visit(i):
        assert i not in seen
        seen.add(i)
        n = nodes[i]
        lo, hi = hull(n['u'], n['v'])
        if not n['children']:
            assert hi < target[0] or target[1] < lo
        else:
            actual = [(nodes[j]['u'], nodes[j]['v']) for j in n['children']]
            assert actual == children(n['u'], n['v'])
            for j in n['children']:
                visit(j)
    visit(0)
    assert len(seen) == len(nodes)


def finite_bundle(u, v, target, epsilon, budget=200000):
    """Outer approximation at a uniform *sum-hull* width, with no greedy choices.

    Every discarded pair is exactly disjoint from target. Every retained
    pair is unresolved, even if their hull union covers the target.
    """
    queue = [(u, v)]
    leaves = []
    visited = 0
    while queue:
        u, v = queue.pop()
        visited += 1
        if visited > budget:
            raise RuntimeError('Finite bundle budget exhausted')
        lo, hi = hull(u, v)
        if hi < target[0] or target[1] < lo:
            continue
        if hi-lo <= epsilon:
            leaves.append((lo, hi))
        else:
            queue.extend(children(u, v))
    components = merge(leaves)
    covers = any(a <= target[0] and target[1] <= b for a, b in components)
    return {'epsilon': str(epsilon), 'visited': visited,
            'unproved_leaves': len(leaves), 'components': len(components),
            'covers_target_at_this_finite_scale_only': covers}


def verify_facts():
    a = Q(-1, F(2, 5))
    b = Q(F(-4, 3), F(2, 3))
    c = Q(F(-1, 2), F(1, 4))
    d = 1/(2+a)
    expected = {'': (a, b), '1': (c, b), '13': (a, d)}
    for s, (lo, hi) in expected.items():
        assert extreme_tail(s, False)[0] == lo
        assert extreme_tail(s, True)[0] == hi

    # In every tail state the gap between the first-digit 3 and 2
    # branches has exactly these endpoints. Both endpoints are attained.
    x, y = 1/(3+a), 1/(2+b)
    bounds = {}
    for s, rmax in [('', F(1, 2)), ('1', F(1)), ('13', F(1, 3))]:
        lo = expected[s][0]
        s3, s2 = step(s, '3'), step(s, '2')
        assert 1/(3+extreme_tail(s3, False)[0]) == x
        assert 1/(2+extreme_tail(s2, True)[0]) == y
        assert lo < x < y < expected[s][1]
        bound = (x-lo)/(y-x)*(1+rmax*y)/(1+rmax*lo)
        bounds[s or 'empty'] = bound
    universal = Q(F(19, 4), F(-5, 4))
    assert max(bounds.values()) == universal < F(4, 5)
    # Analytic monotonicity in r is proved in README; this verifies the
    # endpoint values, not a finite sample masquerading as a uniform proof.
    background = 3+b+d
    assert background == Q(0, F(4, 3)) < F(191, 45)

    target = (F('1.2924533'), F('1.2924537'))
    exclusions = []
    for u, v in [('1121', '122'), ('1122', '122')]:
        nodes = exclusion(u, v, target)
        replay_exclusion(nodes, target)
        exclusions.append({'root': [u, v], 'nodes': nodes})

    # A witness in the excluded target is available from the third branch.
    # Bound its eventually periodic continued fractions independently,
    # using universal rational tail bounds, without arithmetic in sqrt(2).
    u, v = '1123313211', '122123122'
    state_of(u+'2'*80)
    state_of(v+'2'*80)
    def bracket(w):
        return sorted(transform(w+'2'*80, z) for z in (F(1, 4), F(4, 5)))
    left, right = bracket(u), bracket(v)
    witness = (left[0]+right[0], left[1]+right[1])
    assert target[0] < witness[0] <= witness[1] < target[1]
    assert u.startswith('1123') and v.startswith('122')

    return {
        'status': 'Exact obstructions; no certified interior interval',
        'tail_extrema': {s or 'empty': [z.record() for z in ends]
                         for s, ends in expected.items()},
        'thickness_upper_bounds': {s: z.record() for s, z in bounds.items()},
        'uniform_thickness_upper_bound': universal.record(),
        'background_perron_upper_bound': background.record(),
        'excluded_target': [str(t) for t in target],
        'exclusion_certificates': exclusions,
        'third_branch_witness': {'prefixes': [u, v], 'period': '2',
                                 'rational_enclosure': [str(z) for z in witness]},
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--bundle-exponents', type=int, nargs='*', default=[5, 6])
    args = ap.parse_args()
    data = verify_facts()
    data['finite_bundle_target'] = ['1.29288', '1.292906']
    data['finite_bundles'] = []
    for k in args.bundle_exponents:
        result = finite_bundle('112', '122', (F('1.29288'), F('1.292906')), F(1, 10**k))
        data['finite_bundles'].append(result)
        print(json.dumps(result), flush=True)
    print('All exact assertions passed. Interior remains unproved.', flush=True)
    if args.output:
        args.output.write_text(json.dumps(data, indent=2)+'\n')


if __name__ == '__main__':
    main()
