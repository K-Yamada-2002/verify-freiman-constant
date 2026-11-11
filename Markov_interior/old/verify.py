"""Verify the complete Markov interior-interval construction.

Default: regenerate both inputs, replay every adopted row, check
root coverage and all-position bounds, and certify the rational intervals
using the analytic lemmas. No archive or Freiman imports are used.
Run with SageMath's Python; a C++17 compiler is also required.
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from proof import verify_intervals

HERE = Path(__file__).resolve().parent


def run(command):
    # Preserve subprocess diagnostics on failure.
    result = subprocess.run(list(map(str, command)), capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'Command failed: {command}\n'
                           f'{result.stdout[-4000:]}{result.stderr[-4000:]}')
    return result.stdout


def verify_table(data, name, binary, independent_binary, work):
    # Load numeric input, generation metadata, and adopted-row bits.
    source = data / name
    input_path, meta_path = source.with_suffix('.dat'), source.with_suffix('.meta.json')
    alive_path = data / (name + '.alive.bin')
    meta, alive = json.loads(meta_path.read_text()), alive_path.read_bytes()

    # 1. Require one bit per (left state, right state, ratio bin, band type).
    size = len(meta['keys']) ** 2 * (meta['high'] - meta['low'] + 1) * len(meta['bands'])
    adopted = sum(alive)
    if len(alive) != size or any(value not in (0, 1) for value in alive) or not adopted:
        raise ValueError('Invalid or empty adoption array: ' + name)

    # 2. Reproduce numeric input and metadata used by the proof.
    generated = work / (name + '-input')
    command = [sys.executable, '-B', HERE / 'prepare.py', '--output', generated]
    for key in ('memory', 'length', 'spine', 'grid', 'base', 'low', 'high', 'return_length'):
        command.extend(['--' + key.replace('_', '-'), str(meta[key])])
    command.extend(['--forbidden', meta['language'], '--root',
                    ','.join(''.join(map(str, word)) for word in meta['root_words'])])
    if meta.get('macro'):
        command.append('--macro')
    run(command)
    if generated.with_suffix('.dat').read_bytes() != input_path.read_bytes():
        raise ValueError('Regenerated input differs: ' + name)
    generated_meta = json.loads(generated.with_suffix('.meta.json').read_text())
    if any(meta.get(key) != value for key, value in generated_meta.items()
           if key not in ('scope', 'transition_checks')):
        raise ValueError('Regenerated metadata differs: ' + name)
    print(name + ': input reproduced.', file=sys.stderr, flush=True)

    # 3. Passing adopted bits selects fixed-table verification; failed rows cause an error.
    output = work / (name + '-replay.json')
    run([binary, input_path, output, alive_path])
    replay = json.loads(output.read_text())
    if not replay['closed_family_found']:
        raise ValueError('Full fixed-table replay failed: ' + name)
    print(f'{name}: all {adopted:,} adopted rows accepted without deletion.',
          file=sys.stderr, flush=True)

    report = {'language': meta['language'], 'candidate_rows': size, 'adopted_rows': adopted}
    # Optionally audit input semantics and repeat coverage checks with separate implementations.
    if independent_binary:
        semantics = json.loads(run([sys.executable, '-B', '-S', HERE / 'audit.py', input_path, meta_path]))
        # audit.cpp prints progress followed by a final JSON summary.
        coverage = json.loads(run([independent_binary, input_path, alive_path]).splitlines()[-1])
        report['independent'] = {'semantics': semantics, 'coverage': coverage}
        print(name + ': independent audits accepted.', file=sys.stderr, flush=True)
    return report


def verify(data, independent=False, tables_only=False):
    # Assertions in proof.py are part of verification.
    if not __debug__:
        raise RuntimeError('Verification requires Python assertions; do not use -O')

    # Keep binaries and regenerated files in temporary storage.
    with tempfile.TemporaryDirectory(prefix='markov-interior-verify-') as temporary:
        work = Path(temporary)
        binary = work / 'kernel'
        # Compile the main verifier.
        run(['c++', '-O3', '-std=c++17', '-pthread', HERE / 'kernel.cpp', '-o', binary])
        audit_binary = None
        if independent:
            audit_binary = work / 'independent'
            # Compile the independent verifier.
            run(['c++', '-O3', '-std=c++17', HERE / 'audit.cpp', '-o', audit_binary])
        tables = {name: verify_table(data, name, binary, audit_binary, work)
                  for name in ('original', 'table')}

        # Check root coverage, noncentral bounds, and gluing conditions.
        # A separate analytic argument justifies the passage to infinite continued fractions.
        intervals = None if tables_only else verify_intervals(data)
    if intervals:
        print('Root coverage, all noncentral positions, and all three interval claims accepted.',
              file=sys.stderr, flush=True)
    # Emit interval claims only when interval checks ran.
    return {'passed': True,
            'scope': ('Finite-table closure only' if tables_only else
                      'Markov and Lagrange interval inclusions: exact finite verification plus analytic argument'),
            'tables': tables, 'interval_proof': intervals,
            'claims': intervals['claims'] if intervals else []}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=HERE / 'certificates')
    parser.add_argument('--independent', action='store_true',
                        help='Also run independent input-semantics and all-row coverage audits')
    parser.add_argument('--tables-only', action='store_true',
                        help='Explicitly stop before the interval proof; no interval claim is emitted')
    parser.add_argument('--output', type=Path, help='Optionally save the full verification report')
    args = parser.parse_args()
    report = verify(args.data.resolve(), args.independent, args.tables_only)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
