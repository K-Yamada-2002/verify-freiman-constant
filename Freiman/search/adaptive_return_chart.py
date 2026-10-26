"""Adaptive uniform band covering with an explicitly justified return family.

The covering engine certifies a local implication only. Closure additionally
requires a caller-supplied proof that each forced return belongs to the same
family. The digit-3 orbit used below supplies that proof via orbit_box.
"""
import argparse
import heapq
import json
import time
from fractions import Fraction as Q

from endpoint_return import ReturnSearch, A, B, BASE, shape_width, normalized_sum, mix
from periodic_exception import orbit_box
from typed_intervals import E


def thirdigit_family_box(a, b, parent_box, u, w, n):
    """Enclose all ancestors in parent_box followed by u 3^(n+2k), w 3^(n+2k).

    With K_j the continuant of 3^j and t=K_(j-1)/K_j, the common
    K_j cancels from the derivative ratio. Every expression is fractional
    linear in each of r,s,t separately, so corners bound the whole family.
    """
    from exact_cf import matrix
    from obstruction_probe import cf as rational_cf
    from anchor_boxes import anchor
    from math import isqrt
    from itertools import product
    assert n >= 2 and n % 2 == 0
    low = rational_cf((3,) * n, Q(0))
    precision = 10 ** 40
    high = (Q(isqrt(13 * precision ** 2) + 1, precision) - 3) / 2
    assert low * low + 3 * low - 1 <= 0 <= high * high + 3 * high - 1
    assert low <= rational_cf((3, 3), low) <= rational_cf((3, 3), high) <= high
    aa, bb = a + u + (3,) * n, b + w + (3,) * n
    def values(word, ext, child, r, t):
        A, B, C, D = matrix(ext)
        c, d = C + r * A, D + r * B
        denominator = d + c * t
        numerator = d * t + c * (1 - 3 * t)
        assert denominator > 0 and numerator > 0
        h = (denominator + numerator * anchor(child)) / (1 + r * anchor(word))
        assert h > 0
        return numerator / denominator, h
    rb = tuple(sorted(values(a, u, aa, r, t)[0] for r, t in product(parent_box[0], (low, high))))
    sb = tuple(sorted(values(b, w, bb, s, t)[0] for s, t in product(parent_box[1], (low, high))))
    scales = []
    for r, s, t, S in product(parent_box[0], parent_box[1], (low, high), parent_box[2]):
        z = values(a, u, aa, r, t)[1] / values(b, w, bb, s, t)[1]
        scales.append(S * z * z)
    return aa, bb, ((rb[0], rb[-1]), (sb[0], sb[-1]), (min(scales), max(scales)))


def cover(kernel, a, b, box, target, returns, max_nodes=10000, max_length=40,
          seconds=180, split='balanced', overlap_graph=False, initial_rectangles=()):
    start = time.monotonic()
    r, s, S = box
    wa, wb = shape_width(a, r), shape_width(b, s)
    R = S[0] * wb[0] / wa[1], S[1] * wb[1] / wa[0]
    p, q = map(E.cast, target)
    from anchor_boxes import AnchorUniform
    proof = AnchorUniform(a, b, f'band_{target[0]}_{1-target[1]}', box)
    graph_rows = {}
    graph_menu = None
    def vertex(row):
        l, h = map(Q, row['band'])
        return tuple(row['u']), tuple(row['w']), f'band_{l}_{1-h}'
    def graph_try():
        pl, ph = proof.numeric(((), (), proof.kind))
        candidates = [(*proof.numeric(v), *v) for v in graph_rows]
        candidates = [v for v in candidates if v[0] <= ph + 1e-10 and v[1] >= pl - 1e-10]
        return proof.select(candidates)
    caches = ({}, {})
    def side(which, word):
        if word not in caches[which]:
            caches[which][word] = kernel.side((a, b)[which], word, (r, s)[which])
        return caches[which][word]
    def inner(x, y, l, h):
        return (normalized_sum(mix(*x['eta'], l), mix(*y['eta'], l), R)[1],
                normalized_sum(mix(*x['eta'], h), mix(*y['eta'], h), R)[0])
    intervals = []
    for u, w, l, h, destination in returns:
        x, y = side(0, u), side(1, w)
        assert x is not None and y is not None and len(u) + len(w) > 0
        lo, hi = inner(x, y, l, h)
        row = {'u': u, 'w': w, 'band': [str(l), str(h)], 'destination': destination}
        graph_rows[vertex(row)] = row
        if lo <= hi:
            intervals.append((lo, hi, row))
    def merge():
        out = []
        for lo, hi, _ in sorted(intervals, key=lambda z: z[0]):
            if out and lo <= out[-1][1]:
                out[-1] = out[-1][0], max(out[-1][1], hi)
            else:
                out.append((lo, hi))
        return out
    covered = merge()
    queue = [(0, 0, (), ())]
    seen = {((), ())}
    serial = 1
    for u, w in initial_rectangles:
        u, w = tuple(u), tuple(w)
        if (u, w) not in seen:
            seen.add((u, w))
            heapq.heappush(queue, (-1, serial, u, w))
            serial += 1
    visits = 0
    depth_leaves = []
    while queue and visits < max_nodes and time.monotonic() - start < seconds:
        _, _, u, w = heapq.heappop(queue)
        length = len(u) + len(w)
        visits += 1
        x, y = side(0, u), side(1, w)
        if x is None or y is None:
            continue
        outer_lo = normalized_sum(x['eta'][0], y['eta'][0], R)[0]
        outer_hi = normalized_sum(x['eta'][1], y['eta'][1], R)[1]
        if outer_hi < p or q < outer_lo:
            continue
        if any(lo <= max(p, outer_lo) and min(q, outer_hi) <= hi for lo, hi in covered):
            continue
        mapped = S[0] * y['growth'][0] / x['growth'][1], S[1] * y['growth'][1] / x['growth'][0]
        if kernel.base ** kernel.low <= mapped[0] <= mapped[1] <= kernel.base ** (kernel.high + 1):
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
                il, ih = inner(x, y, l, h)
                row = {'u': u, 'w': w, 'band': [str(l), str(h)],
                       'destination': 'kernel', 'geometry': geom,
                       'bins': [lo, hi], 'types': types}
                graph_rows[vertex(row)] = row
                if il <= ih and il <= q and p <= ih:
                    intervals.append((il, ih, row))
            covered = merge()
            if any(lo <= p and q <= hi for lo, hi in covered):
                break
        if length >= max_length:
            depth_leaves.append({'u': u, 'w': w, 'outer': [outer_lo.data(), outer_hi.data()]})
            continue
        if mapped[0] > kernel.base ** (kernel.high + 1):
            choices = (1,)
        elif mapped[1] < kernel.base ** kernel.low:
            choices = (0,)
        elif split == 'both':
            choices = (0, 1)
        else:
            # This only chooses a complete ternary subdivision; it never
            # certifies an inequality. All admissions above are algebraic.
            left_width = float(x['eta'][1][1] - x['eta'][0][0])
            right_width = float((R[0] + R[1]) / 2) * float(y['eta'][1][1] - y['eta'][0][0])
            choices = (0,) if left_width >= right_width else (1,)
        for which in choices:
            for d in (1, 2, 3):
                uu, ww = (u + (d,), w) if which == 0 else (u, w + (d,))
                if (uu, ww) not in seen:
                    seen.add((uu, ww))
                    heapq.heappush(queue, (length + 1, serial, uu, ww))
                    serial += 1
        if visits % 500 == 0:
            print(json.dumps({'visited': visits, 'pending': len(queue), 'seconds': time.monotonic() - start}), flush=True)
        if overlap_graph and visits % 100 == 0:
            graph_menu = graph_try()
            if graph_menu is not None:
                break
    end = p
    menu = []
    while end < q:
        choices = [iv for iv in intervals if iv[0] <= end < iv[1]]
        if not choices:
            break
        best = max(choices, key=lambda z: z[1])
        menu.append(best)
        end = best[1]
    holes = []
    edge = p
    for lo, hi in covered:
        if hi < p or q < lo:
            continue
        if edge < lo:
            holes.append((edge, min(q, lo)))
        edge = max(edge, hi)
    if edge < q:
        holes.append((edge, q))
    if overlap_graph and graph_menu is None and end < q:
        graph_menu = graph_try()
    if graph_menu is not None:
        assert proof.verify(graph_menu)
    return {'local_cover': end >= q or graph_menu is not None, 'target': [str(v) for v in target],
            'cover_method': 'uniform_overlap_graph' if graph_menu is not None else 'uniform_inner_intervals',
            'visited': visits, 'pending': len(queue), 'seconds': time.monotonic() - start,
            'depth_limit_leaves': depth_leaves,
            'menu': [graph_rows[v] for v in graph_menu] if graph_menu is not None else [v[2] for v in menu],
            'candidate_rectangles': sorted({(v[0], v[1]) for v in graph_rows}),
            'uniform_inner_intervals': [] if graph_menu is not None else [[v[0].data(), v[1].data()] for v in menu],
            'uncovered': [] if graph_menu is not None else [[x.data(), y.data()] for x, y in holes],
            'uncovered_decimal': [] if graph_menu is not None else [[float(x), float(y)] for x, y in holes],
            'common_inner_diagnostic_gaps': [[x.data(), y.data()] for x, y in holes]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--kernel', default='graph_wide')
    parser.add_argument('--even-min', type=int, default=12)
    parser.add_argument('--p', default='17/100')
    parser.add_argument('--q', default='19/100')
    parser.add_argument('--nodes', type=int, default=10000)
    parser.add_argument('--length', type=int, default=40)
    parser.add_argument('--seconds', type=float, default=180)
    parser.add_argument('--split', choices=['both', 'balanced'], default='balanced')
    parser.add_argument('--output', default='adaptive_periodic_chart.json')
    args = parser.parse_args()
    kernel = ReturnSearch(args.kernel)
    assert kernel.certified
    a0, b0 = A + (1, 3, 1, 2), B + (3, 1)
    a, b, box = orbit_box(a0, b0, args.even_min)
    p, q = Q(args.p), Q(args.q)
    assert 0 <= p < q <= 1
    result = cover(kernel, a, b, box, (p, q), [((3, 3), (3, 3), p, q, 'same_orbit_family')],
                   args.nodes, args.length, args.seconds, args.split)
    result.update(kernel=args.kernel, a0=a0, b0=b0, even_min=args.even_min,
                  family_closed=result['local_cover'], freiman_ray_proved=False)
    (BASE / args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      ('depth_limit_leaves', 'menu', 'uniform_inner_intervals', 'uncovered')}), flush=True)
