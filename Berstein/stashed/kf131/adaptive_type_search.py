#!/usr/bin/env python3
"""Grow endpoint menus and requested child interval types until closure or a limit.

The C++ engine discovers rules. The separate exact verifier decides whether
a closed candidate is a proof; an open graph is saved for further expansion.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from exact import state_of
from verify_type_graph import Verifier


HERE = Path(__file__).resolve().parent


def summarize(data):
    nodes = data['nodes']
    def kind(node):
        return (tuple(map(state_of, node['states'])), node['parity'],
                tuple(node['lower']), tuple(node['upper']))
    moves = Counter(tuple(edge['suffixes']) for node in nodes if node['covered']
                    for edge in node['children'])
    return {
        'parameterized_types': len(nodes),
        'endpoint_types': len({kind(n) for n in nodes}),
        'locally_covered_candidates': sum(n['covered'] for n in nodes),
        'open_types': sum(not n['covered'] for n in nodes),
        'mixed_parity_types': sum(n['parity'] == -1 for n in nodes),
        'worklist_completed': (data['processed_tasks'] == data['queued_tasks']
                               if 'processed_tasks' in data else None),
        'used_successors': [{'suffixes': list(pair), 'rules': count}
                            for pair, count in moves.most_common()],
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--menu-depths', type=int, nargs='+', default=[1, 2, 3])
    ap.add_argument('--memory', type=int, default=2)
    ap.add_argument('--bins', type=int, default=24)
    ap.add_argument('--base', default='0.88')
    ap.add_argument('--max-step', type=int, default=3)
    ap.add_argument('--rounds', type=int, default=3)
    ap.add_argument('--work-budget', type=int, default=100000)
    ap.add_argument('--pool', choices=('extrema', 'mixed', 'grid'), default='extrema')
    ap.add_argument('--grid-power', type=int, default=4)
    ap.add_argument('--output-dir', type=Path, default=HERE/'adaptive_runs')
    ap.add_argument('--engine', type=Path, help='use an already compiled discovery engine')
    args = ap.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if any(n < 1 for n in args.menu_depths):
        ap.error('menu depths must be positive')
    report = {'status': 'open induction search', 'stages': []}
    with tempfile.TemporaryDirectory(prefix='kf131-types-') as tmp:
        engine = args.engine
        if engine is None:
            compiler = shutil.which('clang++') or shutil.which('g++')
            if compiler is None:
                ap.error('a C++17 compiler is required for discovery')
            engine = Path(tmp)/'search'
            subprocess.run([compiler, '-O3', '-std=c++17', str(HERE/'adaptive_type_search.cpp'),
                            '-o', str(engine)], check=True)
        engine = engine.resolve()
        for depth in sorted(set(args.menu_depths)):
            output = args.output_dir/f'{args.pool}_m{depth}.json'
            command = [str(engine), str(depth), str(args.memory), str(args.bins),
                       args.base, str(args.max_step), str(args.rounds), str(output),
                       str(args.work_budget), args.pool, str(args.grid_power)]
            print(f'Expanding to endpoint menu {depth}', flush=True)
            subprocess.run(command, check=True)
            data = json.loads(output.read_text())
            row = {'menu_depth': depth, 'graph': str(output.resolve()), **summarize(data)}
            checker = Verifier(data)
            if data['closed_candidate']:
                try:
                    row['exact_verification'] = checker.closed()
                    report['status'] = 'closed induction verified exactly'
                except ValueError as error:
                    row['exact_rejection'] = str(error)
            elif data['roots'] and data['nodes'][data['roots'][0]]['covered']:
                try:
                    row['seed_interval'] = checker.seed()
                    row['verified_local_root'] = checker.local(data['roots'][0])
                except ValueError as error:
                    row['exact_rejection'] = str(error)
            report['stages'].append(row)
            (args.output_dir/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
            print(json.dumps({k: row[k] for k in
                              ('menu_depth', 'parameterized_types', 'endpoint_types', 'open_types')}),
                  flush=True)
            if report['status'] == 'closed induction verified exactly':
                break
    print(report['status'], flush=True)


if __name__ == '__main__':
    main()
