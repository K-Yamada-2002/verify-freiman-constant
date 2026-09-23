#!/usr/bin/env python3
"""Automatically try finite induction policies, accepting only exact closure.

Discovery may use floating arithmetic, heuristics, and bounded backtracking.
Only verify_type_graph.Verifier.closed() can change the result to a proof.
An exhausted policy says nothing negative about the actual Cantor sum.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

from adaptive_type_search import summarize
from verify_type_graph import Verifier

HERE = Path(__file__).resolve().parent
DEFAULT_STAGES = [
    dict(menu=2, memory=2, bins=24, base='0.88', variants=4, root_fraction=1),
    dict(menu=2, memory=2, bins=24, base='0.88', variants=12, root_fraction=.25),
    dict(menu=3, memory=2, bins=24, base='0.88', variants=4, root_fraction=.25),
    dict(menu=2, memory=2, bins=72, base='0.96', variants=4, root_fraction=.25, rounds=2),
    dict(menu=2, memory=2, bins=48, base='0.94', variants=8, root_fraction=.25, pool='mixed'),
    dict(menu=2, memory=3, bins=36, base='0.92', variants=4, root_fraction=.25, rounds=2),
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', type=Path, default=HERE/'repair_runs')
    ap.add_argument('--max-types', type=int, default=10000)
    ap.add_argument('--stages', type=int, default=len(DEFAULT_STAGES))
    ap.add_argument('--plan', type=Path, help='JSON list overriding the stage schedule')
    ap.add_argument('--engine', type=Path)
    ap.add_argument('--stage-seconds', type=float, default=600)
    args = ap.parse_args()
    if args.max_types < 1 or args.stages < 1 or args.stage_seconds <= 0:
        ap.error('limits must be positive')
    stages = json.loads(args.plan.read_text()) if args.plan else DEFAULT_STAGES
    args.output_dir.mkdir(parents=True, exist_ok=True)
    sources = ('repair_type_search.py', 'repair_type_search.cpp', 'finite_cover_game.hpp',
               'outer_type_filter.hpp',
               'adaptive_type_search.py', 'adaptive_type_search.cpp',
               'verify_type_graph.py', 'anchored_geometry.py', 'exact.py')
    report = {'status': 'no closed certificate obtained', 'stages': [],
              'source_sha256': {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                for name in sources}}
    with tempfile.TemporaryDirectory(prefix='kf131-repair-') as temporary:
        engine = args.engine
        if engine is None:
            compiler = shutil.which('clang++') or shutil.which('g++')
            if compiler is None:
                ap.error('a C++17 compiler is required')
            engine = Path(temporary)/'repair'
            subprocess.run([compiler, '-O3', '-std=c++17', str(HERE/'repair_type_search.cpp'),
                            '-o', str(engine)], check=True)
        report['engine_sha256'] = hashlib.sha256(engine.read_bytes()).hexdigest()
        report['engine_origin'] = ('provided binary; source hashes are a workspace snapshot'
                                   if args.engine else 'compiled from recorded sources')
        for i, stage in enumerate(stages[:args.stages]):
            cfg = dict(max_step=3, rounds=3, pool='extrema', grid_power=4,
                       max_types=args.max_types, strategy='dfs-reuse',
                       outer_depth=5, outer_samples=3)
            cfg.update(stage)
            cfg.setdefault('outer_max_depth', min(7, cfg['outer_depth']+1))
            cfg.setdefault('root_trials', 64)
            cfg.setdefault('root_step_budget', 5000)
            output = args.output_dir/f'stage_{i+1:02}.json'
            command = [str(engine.resolve())] + [str(cfg[k]) for k in
                       ('menu', 'memory', 'bins', 'base', 'max_step', 'rounds')]
            command += [str(output.resolve())] + [str(cfg[k]) for k in
                        ('max_types', 'variants', 'pool', 'grid_power', 'root_fraction',
                         'strategy', 'outer_depth', 'outer_samples', 'outer_max_depth',
                         'root_trials', 'root_step_budget')]
            row = {'settings': cfg, 'graph': str(output.resolve())}
            start = time.monotonic()
            wall_start = time.time()
            print(f'Stage {i+1}: {json.dumps(cfg)}', flush=True)
            try:
                subprocess.run(command, check=True, timeout=args.stage_seconds)
            except subprocess.TimeoutExpired:
                row['stop'] = 'stage time limit; no proof inferred'
            except subprocess.CalledProcessError as error:
                row['stop'] = f'discovery engine exited {error.returncode}'
            # A time-limited run can still leave a useful atomic checkpoint.
            # Never accidentally reuse a graph left by an older invocation.
            if output.exists() and output.stat().st_mtime >= wall_start:
                try:
                    data = json.loads(output.read_text())
                except (ValueError, OSError) as error:
                    row['invalid_checkpoint'] = str(error)
                else:
                    row.update(summarize(data))
                    row['root_available'] = bool(data['roots'])
                    details = Path(str(output)+'.search.json')
                    if details.exists() and details.stat().st_mtime >= wall_start:
                        row['repair'] = json.loads(details.read_text())
                        progress = row['repair']
                        row['worklist_completed'] = (
                            progress['scheduled_tasks'] == progress['processed_tasks']
                            + progress.get('cancelled_tasks', 0))
                    if data['closed_candidate']:
                        try:
                            row['exact_verification'] = Verifier(data).closed()
                        except ValueError as error:
                            row['exact_rejection'] = str(error)
                        else:
                            report['status'] = 'closed induction verified exactly'
                            (args.output_dir/'proof_audit.json').write_text(
                                json.dumps(row['exact_verification'], indent=2)+'\n')
            row['elapsed_seconds'] = round(time.monotonic()-start, 3)
            report['stages'].append(row)
            (args.output_dir/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
            print(json.dumps({k: v for k, v in row.items()
                              if k in ('repair', 'stop', 'exact_rejection', 'exact_verification')}),
                  flush=True)
            if report['status'] == 'closed induction verified exactly':
                break
    print(report['status'], flush=True)


if __name__ == '__main__':
    main()
