#!/usr/bin/env python3
"""Find and independently replay exact gaps in requested interval families.

Floating point proposes witnesses. Replay enumerates all legal cylinders at
the stated depth and excludes the whole open gap using Q(sqrt(462)) only.
One counterexample n suffices to refute filledness of an all-n obligation.
"""
import argparse
import heapq
import json
from pathlib import Path

from audit_child_covers import audit
from child_family_covers import kind_name, word_pair
from deeper_child_gaps import numeric_sides
from explore import Q, cylinder, extensions, hull, interval_record, state_of
from invariant_boxes import ALL_TYPE_LABELS
from type_certificates import endpoint

HERE = Path(__file__).parent
COVER_FILES = ('child_family_covers.json', 'child_family_covers_deep.json',
               'child_J1_covers.json', 'child_J2R_covers.json',
               'child_H11_1_cover.json', 'child_frontier_covers.json')


def target_interval(u, v, kind):
    if kind == 0:
        return hull(u, v)
    return tuple(sorted(endpoint(u, v, label) for label in ALL_TYPE_LABELS[kind]))


def merged_row(left, right, i):
    """Merge one row before heap-merging the Cartesian sum, using O(N) memory."""
    a, b, _ = left[i]
    lo, hi, lo_j, hi_j = a+right[0][0], b+right[0][1], 0, 0
    for j, (c, d, _) in enumerate(right[1:], 1):
        if a+c <= hi:
            if b+d > hi:
                hi, hi_j = b+d, j
        else:
            yield lo, hi, i, lo_j, hi_j
            lo, hi, lo_j, hi_j = a+c, b+d, j, j
    yield lo, hi, i, lo_j, hi_j


def numeric_gap_candidates(u, v, depth):
    left, right = numeric_sides(u, v, depth)
    intervals = heapq.merge(*(merged_row(left, right, i) for i in range(len(left))))
    current = next(intervals)
    found = []
    for row in intervals:
        if row[0] > current[1]+1e-12:
            found.append((current[1], row[0],
                          (left[current[2]][2], right[current[4]][2]),
                          (left[row[2]][2], right[row[3]][2])))
        if row[1] > current[1]:
            current = row
    return found


def verify_gap(row):
    """Check target membership and exclude every depth-d cylinder sum exactly."""
    u, v = word_pair(row['left_suffix'], row['right_suffix'], row['n'])
    depth = row['depth']
    assert isinstance(depth, int) and depth >= 1
    lo, hi = (Q(x['a'], x['b']) for x in row['gap'])
    tlo, thi = target_interval(u, v, row['kind'])
    assert tlo <= lo < hi <= thi
    sides = []
    for w in (u, v):
        state_of(w)
        sides.append(sorted(cylinder(z) for z in extensions(w, depth)))
    a, b = sides
    i, j, steps = 0, len(b)-1, 0
    while i < len(a) and j >= 0:
        steps += 1
        if a[i][1]+b[j][1] <= lo:
            i += 1
        elif a[i][0]+b[j][0] >= hi:
            j -= 1
        else:
            raise AssertionError('a legal cylinder sum intersects the proposed gap')
    return {'left_cylinders': len(a), 'right_cylinders': len(b), 'steps': steps}


def discover(u, v, kind, n=0, depth=5):
    a, b = word_pair(u, v, n)
    target = target_interval(a, b, kind)
    for _, _, lower_words, upper_words in numeric_gap_candidates(a, b, depth):
        lo = max(hull(*lower_words)[1], target[0])
        hi = min(hull(*upper_words)[0], target[1])
        if not lo < hi:
            continue
        row = {'left_suffix': u, 'right_suffix': v, 'kind': kind,
               'n': n, 'depth': depth, 'gap': interval_record((lo, hi)),
               'boundary_words': [lower_words, upper_words]}
        try:
            row['verification'] = verify_gap(row)
        except AssertionError:
            continue
        return row
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth', type=int, default=5)
    ap.add_argument('--n', type=int, default=0)
    ap.add_argument('--focus', nargs=3)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--verify', type=Path)
    args = ap.parse_args()
    if args.verify:
        rows = json.loads(args.verify.read_text())['obstructions']
        for row in rows:
            verify_gap(row)
        print('verified', len(rows), 'exact obstructions to filledness')
        return
    if args.focus:
        frontier = [(args.focus[0], args.focus[1], int(args.focus[2]))]
    else:
        frontier = audit([json.loads((HERE/name).read_text())
                          for name in COVER_FILES])['unproved_frontier']
    rows = []
    for u, v, k in frontier:
        row = discover(u, v, k, args.n, args.depth)
        print(u or '-', v or '-', kind_name(k), 'GAP' if row else 'no gap detected', flush=True)
        if row:
            rows.append(row)
    result = {'status': 'exact counterexamples; no-gap searches do not prove filledness',
              'surveyed': len(frontier), 'depth': args.depth, 'n': args.n,
              'obstructions': rows}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
