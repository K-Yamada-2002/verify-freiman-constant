#!/usr/bin/env python3
"""Repair uniform local covers by excluding children with known true gaps.

Passing a finite gap search is only a discovery filter, never a filledness
claim. Every returned local cover is replayed by the existing exact verifier.
"""
import argparse
import json
from pathlib import Path

from child_family_covers import geometric_cover, kind_id, verify_row, word_pair
from explore import Q
from frontier_obstructions import HERE, numeric_gap_candidates, target_interval, verify_gap
from search_shape_bank import ShapeSearch, SHAPES8


class GapFilteredSearch(ShapeSearch):
    def __init__(self, obstructions, gap_depth=5):
        super().__init__(max_step=2, shapes=SHAPES8)
        self.gap_depth = gap_depth
        self.known = {}
        for row in obstructions:
            verify_gap(row)
            key = row['left_suffix'], row['right_suffix'], row['n']
            self.known.setdefault(key, []).append(tuple(Q(z['a'], z['b']) for z in row['gap']))

    def _options(self, a, b, depth):
        base_u, base_v = word_pair('', '')
        assert a.startswith(base_u) and b.startswith(base_v)
        u, v = a[len(base_u):], b[len(base_v):]
        a0, b0 = word_pair(u, v, 0)
        gaps = numeric_gap_candidates(a0, b0, self.gap_depth)
        c0 = {c[4]: c for c in self.candidates(a0, b0)}
        answer = []
        for c in self.candidates(a, b):
            if any(max(lo, c0[c[4]][0]) < min(hi, c0[c[4]][1])-1e-12
                   for lo, hi, _, _ in gaps):
                continue
            known = self.known.get((u, v, 0), ())
            if known:
                lo, hi = target_interval(a0, b0, kind_id(c[4]))
                if any(max(lo, x) < min(hi, y) for x, y in known):
                    continue
            answer.append(c)
        return tuple(answer)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gap-depth', type=int, default=5)
    ap.add_argument('--obstructions', type=Path, default=HERE/'induction_obstructions.json')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    search = GapFilteredSearch(json.loads(args.obstructions.read_text())['obstructions'], args.gap_depth)
    # These six parents contain the seven obstructed obligations as children.
    parents = [('11', '1', 0), ('11', '3', 0), ('12', '3', 0),
               ('3', '12', 0), ('3', '1', 4), ('3', '11', 2)]
    rows, failed = [], []
    for u, v, k in parents:
        row = geometric_cover(u, v, k, search, lookahead=0)
        if row is None:
            failed.append((u, v, k))
            print('FAILED', u, v, k, flush=True)
        else:
            verify_row(row)
            rows.append(row)
            print('REPAIRED', u, v, k,
                  [(c['suffixes'], c['name']) for c in row['children']], flush=True)
    result = {'status': 'exact uniform local repairs; NOT a closed induction',
              'shape_bank': 8, 'lookahead_used_only_for_discovery': 0,
              'gap_depth_used_only_for_rejection': args.gap_depth,
              'rule_priority': 100, 'covers': rows, 'failed_searches': failed}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
