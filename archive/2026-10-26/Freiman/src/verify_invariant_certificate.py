"""Regenerate exact input and replay a fixed saved invariant family.

This never repairs a failing family by deleting rows. The final root check
uses algebraic arithmetic independently of the integer overlap verifier.
Run from any working directory; all outputs remain in this directory.
"""
from layout import SRC, BIN, LOGS, artifact_path
import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from layout import DATA

from certified_kernel_input import prepare
from verify_closed_root import verify

BASE = DATA


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('name', nargs='?', default='graph_m2')
    args = parser.parse_args()
    name = args.name
    meta = json.loads((BASE / (name + '.meta.json')).read_text())
    tight = meta.get('prehistory_interval') == ['1/4', '4/5']
    regenerated = name + '_checked_input'
    prepare(name, regenerated, graph=True, tight=tight)
    assert (BASE / (name + '.dat')).read_bytes() == (BASE / (regenerated + '.dat')).read_bytes()
    binary = BIN / 'graph_kernel_verify'
    subprocess.run(['c++', '-std=c++17', '-O3', str(SRC / 'graph_kernel.cpp'),
                    '-o', str(binary)], check=True)
    replay = name + '_replay'
    with (LOGS / (replay + '.log')).open('w') as log:
        subprocess.run([str(binary), str(BASE / (regenerated + '.dat')),
                        str(BASE / (replay + '.json')),
                        str(BASE / (name + '.json.alive.bin'))],
                       stdout=log, check=True)
    root = verify(name, replay)
    (BASE / (name + '_algebraic_replay.json')).write_text(json.dumps(root, indent=2) + '\n')
    filenames = [name + '.dat', name + '.meta.json', name + '.json.alive.bin',
                 replay + '.json', name + '_algebraic_replay.json',
                 'graph_kernel.cpp', 'certified_kernel_input.py', 'verify_closed_root.py', 'layout.py']
    summary = {
        'passed': True,
        'exact_input_reproduced': True,
        'fixed_family_replayed': root['closed_states_replayed'],
        'root_surviving_bands': root['root_surviving_bands'],
        'includes_freiman_endpoint': root['includes_freiman_endpoint'],
        'freiman_ray_proved': False,
        'sha256': {f: hashlib.sha256(artifact_path(f).read_bytes()).hexdigest() for f in filenames},
    }
    (BASE / (name + '_verification_manifest.json')).write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
