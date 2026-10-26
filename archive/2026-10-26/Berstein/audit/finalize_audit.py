"""Bind completed independent audit results and check their mathematical link.

Run the individual verifiers first.  This does not substitute for replaying
them; it refuses changed sources/data and records their combined conclusion.
"""

import hashlib
import json
import sys
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
from independent_input import Exact, cf, extreme, state


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name):
    result = json.loads((HERE / name).read_text())
    require(result['passed'], name + ' did not pass')
    return result


def main():
    inputs = load('independent_input.json')
    kernel = load('independent_kernel_summary.json')
    spectral = load('independent_spectral.json')
    arithmetic = load('independent_arithmetic.json')
    for report in (inputs, kernel):
        for name, digest in report['sha256'].items():
            require(sha(ROOT / name) == digest, 'Changed source/data: ' + name)
    require(sha(HERE / 'independent_spectral.py') == spectral['script_sha256'],
            'Changed spectral audit source')
    require(sha(HERE / 'independent_kernel.cpp') == arithmetic['cpp_source_sha256'],
            'Arithmetic checks concern a different C++ source')
    full = kernel['full_check']
    require(full['geometry_range'] == [0, 484] and full['adopted_rows'] == 3464816
            and full['adopted_cells'] == 150040 and full['failed_cells'] == 0,
            'The entire fixed family was not verified')
    require(inputs['initial_root']['alive_count'] == full['adopted_rows'],
            'Semantic and coverage checks concern different family sizes')
    require(inputs['initial_root']['bands'] == 25 and spectral['near_centers_checked'] == 57054,
            'Incomplete root/spectral check')

    # Verify the exact bulk constant stated in the original mathematical text.
    # This reuses only the independently audited field/CF implementation.
    values = []
    for window in product((1, 2, 3), repeat=5):
        if state(window) is None:
            continue
        left, right = window[:2][::-1], window[3:]
        value = (window[2] + cf(left, extreme(state(window[::-1]), len(left) % 2 == 1))
                 + cf(right, extreme(state(window), len(right) % 2 == 1)))
        values.append((value, window))
    bulk, witness = max(values)
    require(bulk == Exact(0, Q(4, 19)), 'Incorrect stated bulk maximum')
    theta = bulk + Q(1, 3025)
    require(all(Exact(Q(row['upper'])) < theta for row in spectral['core_bounds']),
            'Fixed-core bound exceeds exact theta')
    require(Exact(Q(spectral['near_upper'])) < theta < Q('4.52578'),
            'Noncentral domination fails')

    paths = [
        HERE / name for name in (
            'independent_input.py', 'independent_input.json',
            'independent_kernel.cpp', 'independent_kernel_summary.json',
            'check_independent_kernel.py', 'independent_kernel_controls.json',
            'independent_spectral.py', 'independent_spectral.json',
            'check_independent_arithmetic.py', 'arithmetic_harness.cpp',
            'independent_arithmetic.json', 'finalize_audit.py', 'REPORT.txt',
        )
    ]
    paths.extend(ROOT / 'Freiman/data' / name for name in (
        'graph_wide.dat', 'graph_wide.meta.json', 'graph_wide.json.alive.bin'))
    report = {
        'passed': True,
        'claim': '[4.52578,4.52754] is contained in the classical Markov spectrum below c_F',
        'date': '2026-10-01',
        'coverage_rows': full['adopted_rows'],
        'coverage_cells': full['adopted_cells'],
        'coverage_endpoint_tests': full['endpoint_tests'],
        'construction_math_modules_imported': False,
        'uniform_box_coverage': True,
        'input_semantics_and_symbolic_aliases_verified': True,
        'initial_bands': inputs['initial_root']['bands'],
        'noncentral_values_uniformly_bounded': True,
        'exact_bulk': bulk.pair(),
        'exact_noncentral_bound': theta.pair(),
        'exact_bulk_witness': witness,
        'analytic_steps': [
            'Uniform connected interval covers and child parameter inclusion',
            'Positive progress and bounded derivative ratio force both words to grow',
            'Nested continued-fraction cylinders shrink to the chosen target sum',
            'Every noncentral local value is strictly below each target value',
        ],
        'scope': 'Ordinary mathematical/code audit with a separately implemented full certificate verifier.',
        'sha256': {str(path.relative_to(ROOT)): sha(path) for path in paths},
    }
    (HERE / 'audit_verified.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'sha256'}, indent=2))


if __name__ == '__main__':
    main()
