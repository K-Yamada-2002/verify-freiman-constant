"""Verify the complete Markov interior-interval construction.

Default: regenerate and audit both inputs, replay every adopted row, check
root coverage and all-position bounds, and certify the rational intervals
using the analytic lemmas in PROOF.md. No archive or Freiman imports are used.
Only the standard library and a C++17 compiler are required.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from proof import verify_intervals

HERE = Path(__file__).resolve().parent


def run(command):
    result = subprocess.run(list(map(str, command)), capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'Command failed: {command}\n'
                           f'{result.stdout[-4000:]}{result.stderr[-4000:]}')
    return result.stdout


def verify_table(data, name, binary, independent_binary, work):
    source = data / name
    input_path, meta_path = source.with_suffix('.dat'), source.with_suffix('.meta.json')
    alive_path = data / (name + '.alive.bin')
    meta, alive = json.loads(meta_path.read_text()), alive_path.read_bytes()
    size = len(meta['keys']) ** 2 * (meta['high'] - meta['low'] + 1) * len(meta['bands'])
    if len(alive) != size or any(value not in (0, 1) for value in alive) or not any(alive):
        raise ValueError('Invalid or empty adoption array: ' + name)
    generated = work / (name + '-input')
    command = [sys.executable, '-B', '-S', HERE / 'prepare.py', '--output', generated]
    for key in ('memory', 'length', 'spine', 'grid', 'base', 'low', 'high', 'return_length'):
        command.extend(['--' + key.replace('_', '-'), str(meta[key])])
    command.extend(['--forbidden', meta['language'], '--root',
                    ','.join(''.join(map(str, word)) for word in meta['root_words'])])
    if meta.get('macro'):
        command.append('--macro')
    run(command)
    if generated.with_suffix('.dat').read_bytes() != input_path.read_bytes():
        raise ValueError('Regenerated input differs: ' + name)
    if generated.with_suffix('.meta.json').read_bytes() != meta_path.read_bytes():
        raise ValueError('Regenerated metadata differs: ' + name)
    semantics = json.loads(run([sys.executable, '-B', '-S', HERE / 'audit.py', input_path, meta_path]))
    if not semantics['passed']:
        raise ValueError('Independent input semantics failed: ' + name)
    print(name + ': exact input and independent semantics accepted.', file=sys.stderr, flush=True)
    output = work / (name + '-replay.json')
    run([binary, input_path, output, alive_path])
    replay = json.loads(output.read_text())
    if not (replay['verification_only'] and replay['closed_family_found']
            and not replay['round_limit_reached'] and replay['surviving_states'] == sum(alive)):
        raise ValueError('Full fixed-table replay failed: ' + name)
    if Path(str(output) + '.alive.bin').read_bytes() != alive:
        raise ValueError('Replay changed the family: ' + name)
    print(f'{name}: all {sum(alive):,} adopted rows accepted without deletion.',
          file=sys.stderr, flush=True)
    coverage = None
    if independent_binary:
        coverage = json.loads(run([independent_binary, input_path, alive_path]).splitlines()[-1])
        if not (coverage['passed'] and coverage['adopted_rows'] == sum(alive)
                and coverage['failed_cells'] == 0):
            raise ValueError('Independent all-row audit failed: ' + name)
        print(name + ': independent all-row coverage accepted.', file=sys.stderr, flush=True)
    return {'language': meta['language'], 'candidate_rows': size, 'adopted_rows': sum(alive),
            'input_and_metadata_reproduced': True, 'adoption_array_unchanged': True,
            'independent_input_semantics': semantics, 'independent_coverage': coverage}


def verify(data, independent=False, tables_only=False):
    if not __debug__:
        raise RuntimeError('Verification requires Python assertions; do not use -O')
    files = [HERE / name for name in ('prepare.py', 'kernel.cpp', 'proof.py', 'verify.py',
                                      'audit.py', 'PROOF.md')]
    files += [data / (name + suffix) for name in ('original', 'table')
              for suffix in ('.dat', '.meta.json', '.alive.bin')]
    if not tables_only:
        files.append(data / 'roots.json')
    if independent:
        files.append(HERE / 'audit.cpp')
    hashes = {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in files}
    with tempfile.TemporaryDirectory(prefix='markov-interior-verify-') as temporary:
        work = Path(temporary)
        binary = work / 'kernel'
        run(['c++', '-O3', '-std=c++17', '-pthread', HERE / 'kernel.cpp', '-o', binary])
        audit_binary = None
        if independent:
            audit_binary = work / 'independent'
            run(['c++', '-O3', '-std=c++17', HERE / 'audit.cpp', '-o', audit_binary])
        tables = {name: verify_table(data, name, binary, audit_binary, work)
                  for name in ('original', 'table')}
        intervals = None if tables_only else verify_intervals(data)
    if intervals:
        print('Root coverage, all noncentral positions, and all three interval claims accepted.',
              file=sys.stderr, flush=True)
    if any(hashlib.sha256(path.read_bytes()).hexdigest() != digest for path, digest in hashes.items()):
        raise RuntimeError('Sources or certificates changed during verification')
    def label(path):
        return str(path.relative_to(HERE)) if path.is_relative_to(HERE) else str(path)
    return {'passed': True,
            'scope': ('Finite-table closure only' if tables_only else
                      'Markov and Lagrange interval inclusions: exact finite verification plus PROOF.md'),
            'tables': tables, 'interval_proof': intervals,
            'claims': intervals['claims'] if intervals else [],
            'proof_kind': 'Computer-assisted analytic proof; separate Lean development at repository root',
            'sha256': {label(path): digest for path, digest in hashes.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=HERE / 'certificates')
    parser.add_argument('--independent', action='store_true',
                        help='Also run the separate C++ implementation over both entire tables')
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
