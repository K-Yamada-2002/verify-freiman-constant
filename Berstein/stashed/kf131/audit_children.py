#!/usr/bin/env python3
"""Exact finite outer refinements of the priority-assigned child ranges."""
import json
from pathlib import Path
from exact import extensions, hull, merge
from uniform_cover import ROOT, CHILDREN, PREFIXES
from type_certificates import endpoint


def compute():
    previous = endpoint('112', '122', ROOT[0])
    rows = []
    for i, (du, dv) in enumerate(PREFIXES):
        u, v = '112'+du, '122'+dv
        hi = endpoint('112', '122', CHILDREN[i][1])
        for depth in range(1, 5):
            components = merge(hull(uu, vv)
                               for uu in extensions(u, depth)
                               for vv in extensions(v, depth))
            rows.append({'child': chr(65+i), 'prefixes': [u, v],
                         'depth_per_side': depth,
                         'assigned_range_closure': [previous.record(), hi.record()],
                         'covered_by_outer_approximation_only':
                         any(a <= previous and hi <= b for a, b in components)})
        previous = hi
    return {'status': 'Finite outer checks only; no interval filling inferred', 'rows': rows}


if __name__ == '__main__':
    data = compute()
    Path(__file__).with_suffix('.json').write_text(json.dumps(data, indent=2)+'\n')
    for row in data['rows']:
        print(row['child'], row['depth_per_side'], row['covered_by_outer_approximation_only'])
