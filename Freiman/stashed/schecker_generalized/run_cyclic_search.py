#!/usr/bin/env python3
"""Run expanding finite type menus and verify every saved candidate separately.

Success means exact acceptance of a closed graph, never just a search flag.
The default schedule is bounded; it does not assert that a successful finite
certificate exists. Each stage retains its graph, local audit and settings.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

from verify_cyclic_types import Verifier


PLAN = [
    dict(states=6, bins=25, base='22/25', max_step=1, outer_depth=0, grid=0),
    dict(states=6, bins=25, base='22/25', max_step=2, outer_depth=3, grid=4),
    dict(states=13, bins=40, base='23/25', max_step=2, outer_depth=3, grid=8),
    dict(states=13, bins=72, base='24/25', max_step=3, outer_depth=3, grid=16),
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--plan', type=Path)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--stage-seconds', type=float, default=600)
    ap.add_argument('--max-types', type=int, default=10000)
    ap.add_argument('--max-steps', type=int, default=100000)
    ap.add_argument('--native-executable', type=Path)
    args = ap.parse_args()
    plan = json.loads(args.plan.read_text()) if args.plan else PLAN
    directory = Path(__file__).resolve().parent
    args.output_dir.mkdir(parents=True, exist_ok=True)
    report = dict(status='no closed certificate accepted', stages=[],
                  source_hashes={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in list(directory.glob('*.py'))+list(directory.glob('*.cpp'))})
    allowed = {'states', 'bins', 'base', 'max_step', 'outer_depth', 'grid',
               'variants', 'endpoints', 'outer_samples', 'refinement_rounds',
               'split_count', 'split_depth', 'memory', 'balance', 'prune_supersets',
               'breadth_first', 'no_local_filter', 'no_reuse', 'no_return_offers', 'reuse_pending',
               'edge_grid', 'grow_edge_grid', 'macro_menu', 'shape_menu', 'adaptive_shapes', 'max_shapes',
               'min_cost_cover'}
    for i, settings in enumerate(plan):
        if not set(settings) <= allowed:
            raise ValueError('unknown plan fields')
        # A unique name prevents an interrupted run from loading an older
        # stage's certificate under the same output directory.
        graph = args.output_dir/f'stage-{i+1}-{time.time_ns()}.json'
        command = [sys.executable, str(directory/'search_cyclic_types.py'),
                   '--output', str(graph), '--seconds', str(args.stage_seconds),
                   '--max-types', str(args.max_types), '--max-steps', str(args.max_steps)]
        for key, value in settings.items():
            if isinstance(value, bool):
                if value:
                    command += ['--'+key.replace('_', '-')]
            else:
                command += ['--'+key.replace('_', '-'), str(value)]
        if args.native_executable:
            command += ['--native-executable', str(args.native_executable.resolve()), '--no-local-filter']
        started = time.monotonic()
        row = dict(settings=settings, graph=str(graph.resolve()), accepted=False)
        try:
            result = subprocess.run(command, timeout=args.stage_seconds+60, check=False)
            row['returncode'] = result.returncode
        except subprocess.TimeoutExpired:
            row['hard_timeout'] = True
        row['elapsed_seconds'] = round(time.monotonic()-started, 3)
        if graph.exists():
            data = json.loads(graph.read_text())
            row['search'] = data['search']
            checker = Verifier(data)
            try:
                row['verification'] = checker.closed()
                row['accepted'] = True
                report['status'] = 'closed certificate accepted exactly'
            except ValueError as error:
                row['closure_rejection'] = str(error)
                audit = checker.audit()
                audit_path = graph.with_suffix('.audit.json')
                audit_path.write_text(json.dumps(audit, indent=2)+'\n')
                row['audit'] = dict(path=str(audit_path.resolve()),
                    verified=len(audit['verified_rules']), failed=len(audit['failed_rules']),
                    unresolved=len(audit['open_nodes']))
        report['stages'].append(row)
        (args.output_dir/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(row), flush=True)
        if row['accepted']:
            break


if __name__ == '__main__':
    main()
