#!/usr/bin/env python3
"""Matched exact search: eager child checks versus contact-driven checks.

Both versions use the same input, targets, catalog, BFS order and verifier.
Only the timing of child validation differs. This benchmarks a search kernel,
not end-to-end proof discovery or the universal fallback.
"""
import argparse
import copy
import json
from pathlib import Path
import time

from hybrid_discovery import Mosaic, signature
from search_complete_induction import atomic_json
from verify_piecewise_charts import PiecewiseVerifier


def measure(base, targets, eager):
    lane = copy.deepcopy(base)
    lane.targets = lane.targets[:targets]
    began, prepared = time.perf_counter(), set()
    while not lane.finished:
        if eager:
            node, domain, _, _ = lane.checker.node(lane.targets[lane.position])
            if node['cell'] not in prepared:
                for i in lane.groups[signature(domain)]:
                    key = node['cell'], i
                    lane.statistics['child_checks'] += 1
                    try:
                        lane.checker.child(domain, lane.catalog[i]['edge'])
                    except ValueError:
                        lane.statistics['child_failures'] += 1
                        lane.cache[key] = False
                    else:
                        lane.cache[key] = True
                prepared.add(node['cell'])
        lane.step()
    elapsed = time.perf_counter()-began
    return dict(seconds=elapsed, statistics=copy.deepcopy(lane.statistics),
                proof_hash=PiecewiseVerifier(lane.graph).proof_hash()), lane.graph


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--targets', type=int, default=64)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.targets < 1:
        ap.error('positive target count required')
    graph = json.loads(args.graph.read_text())
    base = Mosaic(graph)
    # Run both orders. Geometry LRU caches can favor the second run, so a
    # single warm run must not be advertised as an unconditional speedup.
    rows, reference = [], None
    for eager in (True, False, False, True):
        for module, names in (
                ('chart_geometry', ('outer', 'relative_box', 'compare')),
                ('type_graph_geometry', ('endpoint',))):
            imported = __import__(module)
            for name in names:
                clear = getattr(getattr(imported, name), 'cache_clear', None)
                if clear:
                    clear()
        record, result = measure(base, args.targets, eager)
        if reference is None:
            reference = result
        if result != reference:
            raise ValueError('search variants produced different results')
        record['mode'] = 'eager' if eager else 'lazy'
        rows.append(record)
        print(json.dumps(record), flush=True)
    atomic_json(args.output, dict(targets=args.targets, results=rows, identical_graphs=True,
                scope='matched kernel, setup/audit excluded; no universal worst-case speed claim'))


if __name__ == '__main__':
    main()
