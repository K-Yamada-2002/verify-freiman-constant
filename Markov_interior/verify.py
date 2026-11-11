"""Regenerate V2 inputs, replay adopted rows, and check the interval proof.

Run with SageMath's Python and a C++17 compiler. The data directory contains
original.dat, original.meta.json, original.alive.bin, the corresponding table.*
files, and roots.json for proof.py.
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def run(command):
    """Run a command and retain its diagnostics if it fails."""
    result = subprocess.run(list(map(str, command)), capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'Command failed: {command}\n'
                           f'{result.stdout[-4000:]}{result.stderr[-4000:]}')
    return result.stdout


def verify_table(data, name, binary, work):
    """Regenerate one V2 input and replay its fixed adoption array."""
    source = data / name
    input_path, meta_path = source.with_suffix('.dat'), source.with_suffix('.meta.json')
    alive_path = data / (name + '.alive.bin')
    meta, alive = json.loads(meta_path.read_text()), alive_path.read_bytes()
    if meta.get('format') != 'FREIMAN_DYADIC_GRAPH_V2':
        raise ValueError('Expected V2 metadata: ' + name)

    # 1. Require one Boolean byte per (left state, right state, ratio bin, band).
    size = len(meta['keys']) ** 2 * (meta['high'] - meta['low'] + 1) * len(meta['bands'])
    adopted = sum(alive)
    if len(alive) != size or any(value not in (0, 1) for value in alive) or not adopted:
        raise ValueError('Invalid or empty adoption array: ' + name)

    # 2. Regenerate the input from its recorded settings.
    # For example, lower_tail_depth=6 becomes --lower-tail-depth 6.
    generated = work / (name + '-input')
    command = [sys.executable, '-B', HERE / 'prepare.py', '--output', generated,
               '--forbidden', meta['language']]
    for key in ('memory', 'length', 'lower_tail_depth', 'grid', 'base', 'low', 'high'):
        command.extend(['--' + key.replace('_', '-'), str(meta[key])])
    if meta['macro']:
        command.append('--macro')
    run(command)
    if generated.with_suffix('.dat').read_bytes() != input_path.read_bytes():
        raise ValueError('Regenerated input differs: ' + name)
    if json.loads(generated.with_suffix('.meta.json').read_text()) != meta:
        raise ValueError('Regenerated metadata differs: ' + name)
    print(name + ': input reproduced.', file=sys.stderr, flush=True)

    # 3. Replay all adopted rows. Kernel failures propagate through run().
    # The kernel writes a JSON report with closed_family_found=true on success.
    output = work / (name + '-replay.json')
    run([binary, input_path, output, alive_path])
    replay = json.loads(output.read_text())
    if not replay['closed_family_found']:
        raise ValueError('Full fixed-table replay failed: ' + name)
    print(f'{name}: all {adopted:,} adopted rows accepted without deletion.',
          file=sys.stderr, flush=True)
    return {'language': meta['language'], 'candidate_rows': size, 'adopted_rows': adopted}


def verify(data, tables_only=False):
    # Assertions in the interval proof must remain enabled.
    if not __debug__:
        raise RuntimeError('Verification requires Python assertions; do not use -O')

    with tempfile.TemporaryDirectory(prefix='markov-interior-v2-verify-') as temporary:
        work = Path(temporary)
        binary = work / 'kernel'
        # Compile the V2 coverage verifier.
        run(['c++', '-O3', '-std=c++17', '-pthread', HERE / 'kernel.cpp', '-o', binary])
        tables = {name: verify_table(data, name, binary, work)
                  for name in ('original', 'table')}

        intervals = None
        if not tables_only:
            # proof.py checks root coverage, noncentral bounds, and interval gluing.
            from proof import verify_intervals

            intervals = verify_intervals(data)
            if not intervals['passed']:
                raise ValueError('Interval verification failed')
            print('Root coverage, noncentral bounds, and interval claims accepted.',
                  file=sys.stderr, flush=True)

    return {'passed': True,
            'scope': ('Finite-table closure only' if tables_only else
                      'Markov and Lagrange interval inclusions: exact finite verification plus analytic argument'),
            'tables': tables, 'interval_proof': intervals,
            'claims': intervals['claims'] if intervals else []}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=HERE / 'certificates',
                        help='Directory containing V2 inputs and proof certificates')
    parser.add_argument('--tables-only', action='store_true',
                        help='Verify finite-table closure and omit the interval proof')
    parser.add_argument('--output', type=Path, help='Save the JSON verification report')
    args = parser.parse_args()
    report = verify(args.data.resolve(), args.tables_only)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
