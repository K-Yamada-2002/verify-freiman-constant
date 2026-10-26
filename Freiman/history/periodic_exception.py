"""A recurrent exception chart for simultaneous repetitions of digit 3.

The state includes the exact word family a0 3^(N+2n), b0 3^(N+2n).
Thus the exceptional successor (33,33) returns by the family definition;
it need not pass an independent-box approximation of the neutral ratio.
Every other successor must enter an already certified invariant kernel.
"""
import argparse
import json
import math
from fractions import Fraction as Q
from itertools import product
from math import isqrt

from endpoint_return import ReturnSearch, A, B, BASE, shape_width
from anchor_boxes import AnchorUniform, anchor
from exact_cf import parameters
from obstruction_probe import scan, cf


def orbit_box(a0, b0, n):
    assert n >= 2 and n % 2 == 0
    r, s, rho = parameters(a0, b0)
    a, b = a0 + (3,) * n, b0 + (3,) * n
    low = cf((3,) * n, Q(0))
    scale = 10 ** 40
    z = isqrt(13 * scale * scale)
    high = (Q(z + 1, scale) - 3) / 2
    # low <= [0;overline{3}] <= high and T_33 preserves this interval.
    assert low * low + 3 * low - 1 <= 0 <= high * high + 3 * high - 1
    assert low <= cf((3, 3), low) <= cf((3, 3), high) <= high
    def ratio(x, t):
        return (t + x * (1 - 3 * t)) / (1 + x * t)
    rb = tuple(sorted(ratio(r, t) for t in (low, high)))
    sb = tuple(sorted(ratio(s, t) for t in (low, high)))
    # S is a positive squared linear-fractional function of t, hence monotone.
    def S(t):
        numerator = 1 + r * t + (t + r * (1 - 3 * t)) * anchor(a)
        denominator = 1 + s * t + (t + s * (1 - 3 * t)) * anchor(b)
        assert numerator > 0 and denominator > 0
        zz = numerator / denominator
        return rho * zz * zz
    box = rb, sb, tuple(sorted(S(t) for t in (low, high)))
    # Direct finite-prefix identity controls the recurrence-coordinate formula.
    for k in (n, n + 2, n + 4):
        aa, bb = a0 + (3,) * k, b0 + (3,) * k
        rr, ss, rrho = parameters(aa, bb)
        t = cf((3,) * k, Q(0))
        assert rr == ratio(r, t) and ss == ratio(s, t)
        zz = (1 + rr * anchor(aa)) / (1 + ss * anchor(bb))
        assert rrho * zz * zz == S(t)
        assert rb[0] <= rr <= rb[1] and sb[0] <= ss <= sb[1]
        assert box[2][0] <= S(t) <= box[2][1]
    return a, b, box


def search(name, n=8, length=4):
    kernel = ReturnSearch(name)
    assert kernel.certified
    a0, b0 = A + (1, 3, 1, 2), B + (3, 1)
    a, b, box = orbit_box(a0, b0, n)
    exts = [u for size in range(length + 1) for u in product((1, 2, 3), repeat=size)]
    left = {u: kernel.side(a, u, box[0]) for u in exts if scan(a + u) is not None}
    right = {u: kernel.side(b, u, box[1]) for u in exts if scan(b + u) is not None}
    target_rows = {}
    for u, x in left.items():
        for w, y in right.items():
            if not 0 < len(u) + len(w) <= length:
                continue
            mapped = (box[2][0] * y['growth'][0] / x['growth'][1],
                      box[2][1] * y['growth'][1] / x['growth'][0])
            if mapped[0] < kernel.base ** kernel.low or mapped[1] > kernel.base ** (kernel.high + 1):
                continue
            lo, hi = kernel.index(mapped[0]), kernel.index(mapped[1])
            if mapped[1] == kernel.base ** hi:
                hi -= 1
            hi = max(lo, hi)
            geom = x['id'] * kernel.sides + y['id']
            available = []
            for typ, l, h in kernel.bands:
                if all(((geom * kernel.bins + i - kernel.low) * kernel.T + typ) in kernel.alive
                       for i in range(lo, hi + 1)):
                    available.append((l, h, typ))
            joined = []
            for l, h, typ in sorted(available):
                if joined and l <= joined[-1][1]:
                    joined[-1][1] = max(joined[-1][1], h)
                    joined[-1][2].append(typ)
                else:
                    joined.append([l, h, [typ]])
            for l, h, types in joined:
                kind = 'F' if (l, h) == (0, 1) else f'band_{l}_{1-h}'
                target_rows[u, w, kind] = {'geometry': geom, 'bins': [lo, hi], 'types': types}
    # Floating values only select rational candidate cutoffs; proof is exact.
    rr, ss, scale = map(lambda x: float((x[0] + x[1]) / 2), box)
    t = (math.sqrt(13) - 3) / 2
    def one(word, r):
        z = float(anchor(word))
        return (-1) ** len(word) * (t - z) * (1 + r * z) / (1 + r * t)
    wa = float(sum(shape_width(a, box[0])) / 2)
    wb = float(sum(shape_width(b, box[1])) / 2)
    point = (one(a, rr) + scale * one(b, ss)) / (wa + scale * wb)
    cut = math.floor(point * 64)
    bands = [(Q(0), Q(1))]
    for radius in (16, 8, 4, 2, 1):
        bands.append((Q(max(0, cut - radius), 64), Q(min(64, cut + 1 + radius), 64)))
    attempts = []
    # Also let the connected component around the return choose its own band.
    # A descending rational grid makes exact stabilization a finite test.
    adaptive = (Q(0), Q(1))
    for attempt in range(len(bands) + 40):
        p, q = bands[attempt] if attempt < len(bands) else adaptive
        kind = 'F' if (p, q) == (0, 1) else f'band_{p}_{1-q}'
        proof = AnchorUniform(a, b, kind, box)
        vertices = list(target_rows) + [((3, 3), (3, 3), kind)]
        candidates = [(*proof.numeric(v), *v) for v in vertices]
        pl, ph = proof.numeric(((), (), kind))
        candidates = [v for v in candidates if v[0] <= ph and v[1] >= pl]
        menu = proof.select(candidates)
        attempts.append({'band': [str(p), str(q)], 'closed': menu is not None,
                         'uniform_comparisons': proof.checks})
        print(json.dumps(attempts[-1]), flush=True)
        if menu is not None:
            assert proof.verify(menu)
            rows = []
            for u, w, ty in menu:
                destination = target_rows.get((u, w, ty))
                if destination is None:
                    assert (u, w, ty) == ((3, 3), (3, 3), kind)
                    destination = 'same_orbit_family_n_plus_1'
                rows.append({'u': u, 'w': w, 'type': ty, 'destination': destination})
            return {'closed': True, 'kernel': name, 'a0': a0, 'b0': b0, 'even_min': n,
                    'band': [str(p), str(q)], 'box': [[str(x) for x in z] for z in box],
                    'menu': rows, 'attempts': attempts, 'freiman_ray_proved': False}
        if attempt < len(bands):
            continue
        loop = ((3, 3), (3, 3), kind)
        all_vertices = [tuple(v[2:]) for v in candidates]
        numeric = {v: proof.numeric(v) for v in all_vertices}
        component = {loop}
        todo = [loop]
        while todo:
            v = todo.pop()
            for w in all_vertices:
                if w in component:
                    continue
                if numeric[v][1] < numeric[w][0] or numeric[w][1] < numeric[v][0]:
                    continue
                if proof.overlap(v, w):
                    component.add(w)
                    todo.append(w)
        grid = 4096
        best_left, best_right = grid + 1, -1
        # Choosing only the numerical extreme candidates can lose a proof,
        # but every accepted grid endpoint is still checked algebraically.
        for v in sorted(component, key=lambda v: numeric[v][0])[:8]:
            child = proof.get(v)[0][0]
            lo, hi = 0, grid
            while lo <= hi:
                mid = (lo + hi) // 2
                endpoint = proof.get(((), (), f'band_{Q(mid,grid)}_{1-Q(mid,grid)}'))[0][0]
                if proof.ge(endpoint, child):
                    best_left = min(best_left, mid)
                    hi = mid - 1
                else:
                    lo = mid + 1
        for v in sorted(component, key=lambda v: numeric[v][1], reverse=True)[:8]:
            child = proof.get(v)[0][1]
            lo, hi = 0, grid
            while lo <= hi:
                mid = (lo + hi) // 2
                endpoint = proof.get(((), (), f'band_{Q(mid,grid)}_{1-Q(mid,grid)}'))[0][1]
                if proof.ge(child, endpoint):
                    best_right = max(best_right, mid)
                    lo = mid + 1
                else:
                    hi = mid - 1
        adaptive = max(p, Q(best_left, grid)), min(q, Q(best_right, grid))
        if adaptive[0] >= adaptive[1] or adaptive == (p, q):
            break
    return {'closed': False, 'kernel': name, 'a0': a0, 'b0': b0, 'even_min': n,
            'limiting_point_normalized_approximation': point, 'attempts': attempts,
            'freiman_ray_proved': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--kernel', default='graph_m2')
    parser.add_argument('--even-min', type=int, default=8)
    parser.add_argument('--length', type=int, default=4)
    parser.add_argument('--output', default='periodic_exception.json')
    args = parser.parse_args()
    result = search(args.kernel, args.even_min, args.length)
    (BASE / args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)
