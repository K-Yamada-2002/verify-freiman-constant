"""Verify the complete Freiman Hall-ray construction.

Always regenerate the exact input, audit its semantics, replay every adopted
row without deletion, and check local endpoint conditions, entry covers,
noncentral bounds and the entire ray. See ../doc/lemma2_schecker.tex for the infinite argument.
Only the standard library and a C++17 compiler are required.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from proof import verify_ray

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent / 'doc' / 'lemma2_schecker.tex'


def run(command):
    result = subprocess.run(list(map(str, command)), capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'Command failed: {command}\n'
                           f'{result.stdout[-4000:]}{result.stderr[-4000:]}')
    return result.stdout


def verify_table(data, binary, independent_binary, work):
    input_path = data / 'graph_wide.dat'
    meta_path = data / 'graph_wide.meta.json'
    alive_path = data / 'graph_wide.alive.bin'
    meta, alive = json.loads(meta_path.read_text()), alive_path.read_bytes()
    size = len(meta['side_keys'])**2 * (meta['high'] - meta['low'] + 1) * len(meta['bands'])
    if len(alive) != size or any(value not in (0,1) for value in alive) or not any(alive):
        raise ValueError('Invalid or empty adoption array')
    generated = work / 'input'
    run([sys.executable, '-B', '-S', HERE / 'prepare.py', '--metadata', meta_path,
         '--output', generated])
    if generated.with_suffix('.dat').read_bytes() != input_path.read_bytes():
        raise ValueError('Regenerated numeric input differs')
    if generated.with_suffix('.meta.json').read_bytes() != meta_path.read_bytes():
        raise ValueError('Regenerated metadata differs')
    semantics = json.loads(run([sys.executable, '-B', '-S', HERE / 'audit.py', input_path, meta_path]))
    if not semantics['passed']:
        raise ValueError('Independent input semantics failed')
    print('Exact input and independent semantics accepted.', file=sys.stderr, flush=True)
    output = work / 'replay.json'
    run([binary, input_path, output, alive_path])
    replay = json.loads(output.read_text())
    if not (replay['verification_only'] and replay['closed_family_found']
            and replay['surviving_states'] == sum(alive)
            and replay['round_counts'] == [sum(alive)]):
        raise ValueError('Full fixed-table replay failed')
    if Path(str(output) + '.alive.bin').read_bytes() != alive:
        raise ValueError('Replay changed the family')
    print(f'All {sum(alive):,} adopted rows accepted without deletion.', file=sys.stderr, flush=True)
    coverage = None
    if independent_binary:
        coverage = json.loads(run([independent_binary, input_path, alive_path]).splitlines()[-1])
        if not (coverage['passed'] and coverage['adopted_rows'] == sum(alive)
                and coverage['failed_cells'] == 0):
            raise ValueError('Independent all-row audit failed')
        print('Independent all-row coverage accepted.', file=sys.stderr, flush=True)
    return {'language': '31313', 'candidate_rows': size, 'adopted_rows': sum(alive),
            'input_and_metadata_reproduced': True, 'adoption_array_unchanged': True,
            'independent_input_semantics': semantics, 'independent_coverage': coverage}


def verify(data, independent=False, table_only=False):
    if not __debug__:
        raise RuntimeError('Verification requires Python assertions; do not use -O')
    files = [HERE / name for name in ('prepare.py', 'kernel.cpp', 'proof.py', 'verify.py',
                                      'audit.py')]
    files.append(PAPER)
    files += [data / ('graph_wide' + suffix) for suffix in ('.dat','.meta.json','.alive.bin')]
    if not table_only:
        files.append(data / 'ray.json')
    if independent:
        files.append(HERE / 'audit.cpp')
    hashes = {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in files}
    with tempfile.TemporaryDirectory(prefix='freiman-verify-') as temporary:
        work = Path(temporary)
        binary = work / 'kernel'
        run(['c++', '-O3', '-std=c++17', HERE / 'kernel.cpp', '-o', binary])
        audit_binary = None
        if independent:
            audit_binary = work / 'independent'
            run(['c++', '-O3', '-std=c++17', HERE / 'audit.cpp', '-o', audit_binary])
        table = verify_table(data, binary, audit_binary, work)
        ray = None if table_only else verify_ray(data, table['adopted_rows'])
    if ray:
        print('Endpoint conditions, initial covers, all noncentral positions and the ray accepted.',
              file=sys.stderr, flush=True)
    if any(hashlib.sha256(path.read_bytes()).hexdigest() != digest for path,digest in hashes.items()):
        raise RuntimeError('Sources or certificates changed during verification')
    def label(path):
        if path.is_relative_to(HERE):
            return str(path.relative_to(HERE))
        if path.is_relative_to(HERE.parent):
            return str(Path('..') / path.relative_to(HERE.parent))
        return str(path)
    return {'passed': True,
            'scope': ('Finite-table closure only' if table_only else
                      'Freiman ray inclusion: exact finite verification plus ../doc/lemma2_schecker.tex'),
            'table': table, 'ray_proof': ray,
            'claims': [ray['claim']] if ray else [],
            'proof_kind': 'Computer-assisted analytic proof; not a Lean formalization of the whole ray',
            'sha256': {label(path): digest for path,digest in hashes.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=HERE / 'certificates')
    parser.add_argument('--independent', action='store_true',
                        help='Also run the separate C++ implementation over the whole table')
    parser.add_argument('--table-only', action='store_true',
                        help='Explicitly stop before the ray proof; no ray claim is emitted')
    parser.add_argument('--output', type=Path, help='Optionally save the full verification report')
    args = parser.parse_args()
    report = verify(args.data.resolve(), args.independent, args.table_only)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
