"""Discover fixed finite entrances from saved Hall bands to graph_wide.

This does not change either invariant kernel or the original ray certificate.
Every accepted child is checked at its actual rational past coordinates and
exact algebraic scale.  Replay is implemented separately below.
"""
import argparse
import heapq
import json
import time
from functools import lru_cache
from fractions import Fraction as Q

from layout import DATA
from exact_cf import interval, union, side_endpoint
from endpoint_return import ReturnSearch
from bridge_search import point_bands
from obstruction_probe import scan
from verify_hall_ray import check_row


@lru_cache(maxsize=200000)
def hull(a, b):
    return interval(a, b)


def joined_point_bands(kernel, a, b):
    bands = point_bands(kernel, a, b)
    result = []
    for p, q, proof in sorted(bands, key=lambda v: (v[0], v[1])):
        if result and p <= result[-1][1]:
            result[-1][1] = max(q, result[-1][1])
            result[-1][2].append({'band': [str(p), str(q)], **proof})
        else:
            result.append([p, q, [{'band': [str(p), str(q)], **proof}]])
    return result


def discover(kernel, a, b, target, nodes, seconds, depth):
    low, high = hull(a, b)
    p, q = map(Q, target)
    low, high = low + p * (high-low), low + q * (high-low)
    start = time.monotonic()
    queue = [(0, 0, (), ())]
    serial = 1
    intervals = []
    merged = []
    visits = 0
    while queue and visits < nodes and time.monotonic()-start < seconds:
        length, _, u, w = heapq.heappop(queue)
        visits += 1
        aa, bb = a+u, b+w
        if scan(aa) is None or scan(bb) is None:
            continue
        outer_low, outer_high = hull(aa, bb)
        if outer_high < low or high < outer_low:
            continue
        if any(l <= max(low, outer_low) and min(high, outer_high) <= h for l, h in merged):
            continue
        for p1, q1, proofs in joined_point_bands(kernel, aa, bb):
            l, h = outer_low+p1*(outer_high-outer_low), outer_low+q1*(outer_high-outer_low)
            if h < low or high < l:
                continue
            row = {'a': ''.join(map(str, aa)), 'b': ''.join(map(str, bb)),
                   'u': list(u), 'w': list(w), 'band': [str(p1), str(q1)],
                   'interval': [l.data(), h.data()], 'proofs': proofs}
            # Independently reproduce all destination checks before saving.
            assert check_row(row, {'graph_wide': kernel}) == (l, h)
            intervals.append((l, h, row))
        merged = union([(l, h) for l, h, _ in intervals])
        if any(l <= low and high <= h for l, h in merged):
            break
        if length >= depth:
            continue
        # Only choose subdivision; all admissions and overlaps above are exact.
        left_width = side_endpoint(aa, False)-side_endpoint(aa, True)
        right_width = side_endpoint(bb, False)-side_endpoint(bb, True)
        side = 0 if float(left_width) >= float(right_width) else 1
        for digit in (1, 2, 3):
            uu, ww = (u+(digit,), w) if side == 0 else (u, w+(digit,))
            heapq.heappush(queue, (length+1, serial, uu, ww))
            serial += 1
    edge = low
    chosen = []
    while edge < high:
        candidates = [v for v in intervals if v[0] <= edge < v[1]]
        if not candidates:
            break
        row = max(candidates, key=lambda v: v[1])
        chosen.append(row[2])
        edge = row[1]
    gaps = []
    edge2 = low
    for l, h in merged:
        if h < low or high < l:
            continue
        if edge2 < l:
            gaps.append([edge2.data(), min(l, high).data()])
        edge2 = max(edge2, h)
    if edge2 < high:
        gaps.append([edge2.data(), high.data()])
    return {'a': ''.join(map(str, a)), 'b': ''.join(map(str, b)), 'band': list(target),
            'interval': [low.data(), high.data()], 'covered': edge >= high,
            'visits': visits, 'pending': len(queue), 'seconds': time.monotonic()-start,
            'menu': chosen, 'gaps': gaps}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--nodes', type=int, default=1000)
    parser.add_argument('--seconds', type=float, default=20)
    parser.add_argument('--depth', type=int, default=16)
    parser.add_argument('--roots', default='')
    parser.add_argument('--output', default='wide_bootstrap_certificate.json')
    args = parser.parse_args()
    source = json.loads((DATA/'hall_ray_certificate.json').read_text())
    kernel = ReturnSearch('graph_wide')
    kernel.name = 'graph_wide'
    assert kernel.certified
    targets = {}
    direct = 0
    for chain in ('finite_chain', 'translation_chain'):
        for i, row in enumerate(source[chain]):
            test = {**row, 'proofs': [p for p in row['proofs'] if p['kernel'] == 'graph_wide']}
            try:
                check_row(test, {'graph_wide': kernel})
                direct += 1
            except AssertionError:
                key = row['a'], row['b'], tuple(row['band'])
                targets.setdefault(key, []).append([chain, i])
    requested = set(args.roots.split(',')) if args.roots else None
    results = []
    for key, uses in targets.items():
        if requested is not None and key[0]+'_'+key[1] not in requested:
            continue
        a, b = (tuple(map(int, x)) for x in key[:2])
        result = discover(kernel, a, b, key[2], args.nodes, args.seconds, args.depth)
        result['source_rows'] = uses
        results.append(result)
        report = {'discovery_only': True, 'kernel': 'graph_wide', 'direct_rows': direct,
                  'required_bootstraps': len(targets), 'results': results,
                  'all_bootstraps_covered': len(results) == len(targets) and all(r['covered'] for r in results)}
        (DATA/args.output).write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({k: v for k, v in result.items() if k not in ('menu', 'gaps')}), flush=True)
    print('COMPLETE', sum(r['covered'] for r in results), len(results), flush=True)


if __name__ == '__main__':
    main()
