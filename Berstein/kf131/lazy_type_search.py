#!/usr/bin/env python3
"""Bounded parallel runs of on-demand induction search, with exact acceptance."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading
import time

from adaptive_type_search import summarize
from verify_type_graph import Verifier
from verify_scalar_graph import ScalarVerifier
from feedback_resume import write_frontier

HERE = Path(__file__).resolve().parent
DEFAULT = [
    dict(menu=2, memory=5, bins=144, base='0.98', lookahead=0),
    dict(menu=3, memory=4, bins=288, base='0.99', lookahead=0),
    dict(menu=2, memory=3, bins=144, base='0.98', lookahead=1),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--plan', type=Path)
    ap.add_argument('--engine', type=Path)
    ap.add_argument('--method', choices=('lazy', 'atlas', 'block', 'feedback'), default='lazy')
    ap.add_argument('--output-dir', type=Path, default=HERE/'lazy_runs')
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--stage-seconds', type=float, default=300)
    args = ap.parse_args()
    if args.jobs < 1 or args.stage_seconds <= 0:
        ap.error('positive job and time limits required')
    stages = json.loads(args.plan.read_text()) if args.plan else DEFAULT
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source_names = ('lazy_type_search.py', 'lazy_type_search.cpp', 'atlas_type_search.cpp',
                    'block_type_search.cpp', 'scalar_discovery_geometry.hpp', 'block_known_cover.hpp',
                    'feedback_type_search.cpp', 'feedback_registry.hpp', 'feedback_frontier.hpp',
                    'feedback_resume.py', 'realize_type_seed.hpp', 'point_sieve.hpp',
                    'ratio_refinement.hpp', 'weighted_interval_cover.hpp', 'feedback_learning.hpp', 'alternative_cover_game.hpp', 'global_frontier.hpp',
                    'dyadic_cover_search.hpp', 'repair_type_search.cpp',
                    'adaptive_type_search.cpp', 'finite_cover_game.hpp', 'outer_type_filter.hpp',
                    'verify_type_graph.py', 'verify_scalar_graph.py', 'scalar_geometry.py',
                    'anchored_geometry.py', 'exact.py')
    report = dict(status='no closed certificate obtained', jobs=args.jobs, stages=[],
                  source_sha256={name: digest(HERE/name) for name in source_names})
    success = threading.Event()
    with tempfile.TemporaryDirectory(prefix='kf131-lazy-') as tmp:
        engine = args.engine
        if engine is None:
            compiler = shutil.which('clang++') or shutil.which('g++')
            if compiler is None:
                ap.error('a C++17 compiler is required')
            engine = Path(tmp)/'lazy'
            subprocess.run([compiler, '-O3', '-std=c++17', str(HERE/(args.method+'_type_search.cpp')),
                            '-o', str(engine)], check=True)
        engine = engine.resolve()
        report['engine_sha256'] = digest(engine)
        report['engine_origin'] = ('provided binary; source hashes describe the workspace'
                                   if args.engine else 'compiled from recorded sources')

        def run(index, stage):
            cfg = dict(max_step=3, max_types=300000, variants=8, outer_depth=4,
                       samples=3, root_trials=128, root_steps=10000,
                       max_cells=100000, seconds=args.stage_seconds, planner='adaptive',
                       pool='extrema', grid_power=9, scalar_grid=2048, box_penalty=64,
                       minimum_memory=0)
            cfg.update(stage)
            cfg.setdefault('entry_depth', cfg['outer_depth'])
            cfg.setdefault('entry_samples', 1)
            output = args.output_dir/f'stage_{index+1:02}.json'
            log = args.output_dir/f'stage_{index+1:02}.log'
            row = dict(stage=index+1, settings=cfg, graph=str(output.resolve()),
                       log=str(log.resolve()))
            if success.is_set():
                return dict(**row, stop='not started: another stage has an exact proof')
            resume_file = None
            if 'resume_graph' in cfg:
                if args.method != 'feedback':
                    raise ValueError('frontier import requires the feedback method')
                resume_file = Path(tmp)/f'resume_{index}.txt'
                row['resume'] = write_frontier(cfg['resume_graph'], resume_file, cfg)
            command = [str(engine)] + [str(cfg[k]) for k in
                      ('menu', 'memory', 'bins', 'base', 'max_step')]
            command += [str(output.resolve())] + [str(cfg[k]) for k in
                       ('max_types', 'variants', 'outer_depth', 'samples', 'lookahead',
                        'root_trials', 'root_steps', 'max_cells', 'seconds')]
            command.append(cfg['planner'])
            command += [cfg['pool'], str(cfg['grid_power'])]
            command.append(str(cfg['scalar_grid']))
            command.append(str(cfg['box_penalty']))
            command.append(str(cfg['minimum_memory']))
            command += [str(cfg['entry_depth']), str(cfg['entry_samples'])]
            if args.method in ('block', 'feedback'):
                cfg.setdefault('root_left', '112'+'2'*cfg['memory'])
                cfg.setdefault('root_right', '122'+'2'*cfg['memory'])
            if 'root_left' in cfg or 'root_right' in cfg:
                if args.method not in ('atlas', 'block', 'feedback') or not all(k in cfg for k in ('root_left', 'root_right')):
                    raise ValueError('custom roots require atlas/block and both root prefixes')
                command += [cfg['root_left'], cfg['root_right']]
            if args.method in ('block', 'feedback'):
                command += [str(cfg.get('block_span', 32)), str(int(cfg.get('tight_preimages', True))),
                            str(cfg.get('probe_percent', 20)), str(cfg.get('scheduler', 0)),
                            str(cfg.get('subgrid_depth', 0))]
            if args.method == 'feedback':
                command += [str(cfg.get('round_steps', 5000)), str(cfg.get('expansion_limit', 2048)),
                            str(cfg.get('round_seconds', 10)), str(cfg.get('repair_mode', 1)),
                            str(cfg.get('sieve_depth', 0)), str(cfg.get('sieve_points', 5)),
                            str(int(cfg.get('trim_known_ranges', True)))]
                command += [str(resume_file) if resume_file else '-',
                            str(cfg.get('ratio_depth', 0)),
                            str(int(cfg.get('ratio_clip_first', True))),
                            str(int(cfg.get('direct_hull_filter', True))),
                            str(int(cfg.get('piece_cache', False))),
                            str(cfg.get('learning_weight', 0)),
                            str(cfg.get('learning_state', '-')),
                            str(int(cfg.get('retain_alternatives', False))),
                            str(int(cfg.get('reuse_alternatives', True))),
                            str(cfg.get('global_mode', 0)),
                            str(cfg.get('global_batch', 512)),
                            str(cfg.get('global_state', '-')),
                            str(cfg.get('return_penalty', 32))]
            if 'global_state' in cfg:
                row['global_input_sha256'] = digest(Path(cfg['global_state']))
            if 'learning_state' in cfg:
                row['learning_input_sha256'] = digest(Path(cfg['learning_state']))
            started, wall_started = time.monotonic(), time.time()
            print(f'Stage {index+1}: {json.dumps(cfg)}', flush=True)
            with log.open('w') as stream:
                try:
                    subprocess.run(command, check=True, timeout=cfg['seconds']+30,
                                   stdout=stream, stderr=subprocess.STDOUT)
                except subprocess.TimeoutExpired:
                    row['stop'] = 'external time limit; retained checkpoint only'
                except subprocess.CalledProcessError as error:
                    row['stop'] = f'engine exit {error.returncode}'
            if output.exists() and output.stat().st_mtime >= wall_started:
                data = json.loads(output.read_text())
                scalar = data.get('schema') == 'kf131-scalar-atlas-v1'
                if scalar:
                    row.update(parameterized_types=len(data['nodes']), open_types=data['open_nodes'],
                               locally_covered_candidates=sum(n['covered'] for n in data['nodes']))
                else:
                    row.update(summarize(data))
                row['graph_sha256'] = digest(output)
                dictionary = Path(str(output)+'.catalog.json')
                if dictionary.exists(): row['catalog_sha256'] = digest(dictionary)
                global_history = Path(str(output)+'.global.txt')
                if global_history.exists(): row['global_output_sha256'] = digest(global_history)
                learned = Path(str(output)+'.learning.txt')
                if learned.exists(): row['learning_output_sha256'] = digest(learned)
                row['root_available'] = bool(data['roots'])
                for suffix, name in (('.search.json', 'repair'), ('.lazy.json', 'lazy'),
                                     ('.feedback.json', 'feedback')):
                    path = Path(str(output)+suffix)
                    if path.exists() and path.stat().st_mtime >= wall_started:
                        row[name] = json.loads(path.read_text())
                if 'repair' in row:
                    r = row['repair']
                    row['worklist_completed'] = (r['scheduled_tasks'] == r['processed_tasks']
                                                 + r.get('cancelled_tasks', 0))
                if data['closed_candidate']:
                    try:
                        row['exact_verification'] = (ScalarVerifier if scalar else Verifier)(data).closed()
                    except ValueError as error:
                        row['exact_rejection'] = str(error)
                    else:
                        success.set()
                        proof_path = args.output_dir/f'stage_{index+1:02}.proof.json'
                        proof_path.write_text(json.dumps(row['exact_verification'], indent=2)+'\n')
            row['elapsed_seconds'] = round(time.monotonic()-started, 3)
            row['log_sha256'] = digest(log)
            print(json.dumps({k: row[k] for k in ('stage', 'elapsed_seconds', 'parameterized_types',
                                                 'open_types', 'lazy', 'exact_verification',
                                                 'exact_rejection', 'stop') if k in row}), flush=True)
            return row

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = [pool.submit(run, i, stage) for i, stage in enumerate(stages)]
            for task in as_completed(pending):
                report['stages'].append(task.result())
                report['stages'].sort(key=lambda row: row['stage'])
                if success.is_set(): report['status'] = 'closed induction verified exactly'
                temporary = args.output_dir/'summary.json.tmp'
                temporary.write_text(json.dumps(report, indent=2)+'\n')
                temporary.replace(args.output_dir/'summary.json')
    print(report['status'], flush=True)


if __name__ == '__main__':
    main()
