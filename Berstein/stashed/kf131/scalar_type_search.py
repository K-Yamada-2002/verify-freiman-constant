#!/usr/bin/env python3
"""Run decreasing scalar-grid searches and exactly verify any closed graph."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent
DEFAULT = [dict(memory=2, bins=24, base='0.88', max_step=3, grid=2048, rounds=80),
           dict(memory=2, bins=72, base='0.96', max_step=3, grid=8192, rounds=80)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--plan', type=Path)
    ap.add_argument('--engine', type=Path)
    ap.add_argument('--output-dir', type=Path, default=HERE/'scalar_runs')
    ap.add_argument('--stage-seconds', type=float, default=600)
    args = ap.parse_args()
    if args.stage_seconds <= 0:
        ap.error('time limit must be positive')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    stages = json.loads(args.plan.read_text()) if args.plan else DEFAULT
    sources = ('scalar_type_search.py', 'scalar_type_search.cpp',
               'adaptive_type_search.cpp', 'scalar_geometry.py',
               'verify_scalar_graph.py', 'anchored_geometry.py', 'verify_type_graph.py', 'exact.py')
    report = dict(status='no closed certificate obtained', stages=[], source_sha256={
        name: hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in sources})
    with tempfile.TemporaryDirectory(prefix='kf131-scalar-') as tmp:
        engine = args.engine
        if engine is None:
            compiler = shutil.which('clang++') or shutil.which('g++')
            if compiler is None:
                ap.error('C++17 compiler required')
            engine = Path(tmp)/'scalar'
            subprocess.run([compiler, '-O3', '-std=c++17', str(HERE/'scalar_type_search.cpp'),
                            '-o', str(engine)], check=True)
        report['engine_sha256'] = hashlib.sha256(engine.read_bytes()).hexdigest()
        report['engine_origin'] = ('provided binary; source hashes are a workspace snapshot'
                                   if args.engine else 'compiled from recorded sources')
        for i, cfg in enumerate(stages):
            output = args.output_dir/f'stage_{i+1:02}.json'
            command = [str(engine.resolve())] + [str(cfg[k]) for k in
                       ('memory', 'bins', 'base', 'max_step', 'grid', 'rounds')] + [str(output.resolve())]
            row = dict(settings=cfg, graph=str(output.resolve()))
            started, wall_started = time.monotonic(), time.time()
            print(f'Stage {i+1}: {json.dumps(cfg)}', flush=True)
            try:
                subprocess.run(command, check=True, timeout=args.stage_seconds)
            except subprocess.TimeoutExpired:
                row['stop'] = 'stage time limit'
            except subprocess.CalledProcessError as error:
                row['stop'] = f'engine exit {error.returncode}'
            if output.exists() and output.stat().st_mtime >= wall_started:
                data = json.loads(output.read_text())
                row.update(nodes=len(data['nodes']), open_nodes=data['open_nodes'], history=data['history'])
                row['candidate_family_exhausted'] = bool(data['history'] and
                                                         data['history'][-1]['active_cells'] == 0)
                if data['closed_candidate']:
                    try:
                        row['exact_verification'] = ScalarVerifier(data).closed()
                    except ValueError as error:
                        row['exact_rejection'] = str(error)
                    else:
                        report['status'] = 'closed induction verified exactly'
            row['elapsed_seconds'] = round(time.monotonic()-started, 3)
            report['stages'].append(row)
            (args.output_dir/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
            if report['status'] == 'closed induction verified exactly':
                break
    print(report['status'], flush=True)


if __name__ == '__main__':
    main()
