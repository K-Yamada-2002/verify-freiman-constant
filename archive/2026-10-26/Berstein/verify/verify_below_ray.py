"""Exact proof of [4.52578,4.52754] subset M below c_F.

Freiman's 31313 closed family is a read-only dependency, distinct from K_F
(131 forbidden). --full regenerates its input and replays every adopted row.
All outputs are in Berstein. No floating point is used for acceptance.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'Berstein'
FREIMAN = ROOT / 'Freiman'
sys.path.insert(0, str(FREIMAN / 'src'))
from exact_cf import K, CF, interval, parameters, union
from endpoint_return import ReturnSearch
from verify_hall_ray import check_row
from spectral_bounds import bound_root
from layout import artifact_path

A, B = (3, 2, 2), (4, 3, 1)
TARGET = Q('4.52578'), Q('4.52754')
BAD = (3, 1, 3, 1, 3)


def legal(word):
    return all(word[i:i+5] != BAD for i in range(len(word)-4))


def rational_cf(word, tail):
    for digit in reversed(word):
        tail = 1 / (digit + tail)
    return tail


@lru_cache(None)
def rational_tail(history, minimize, digits=40):
    """Independent alternating-lexicographic extreme; enclose by [0,1]."""
    tail = []
    for n in range(digits):
        choices = [d for d in (1, 2, 3) if legal(history + tuple(tail) + (d,))]
        d = max(choices) if minimize == (n % 2 == 0) else min(choices)
        tail.append(d)
    return tuple(sorted(rational_cf(tail, t) for t in (Q(0), Q(1))))


def rational_maximum(prefix, history):
    lo, hi = rational_tail(history[-4:], len(prefix) % 2 == 1)
    return max(rational_cf(prefix, t) for t in (lo, hi))


def independent_spectral_audit():
    # A length-five window separates the two continuation constraints.
    bulk = []
    for w in product((1, 2, 3), repeat=5):
        if legal(w):
            value = w[2] + rational_maximum(w[:2][::-1], w[::-1]) + rational_maximum(w[3:], w)
            bulk.append((value, w))
    bulk_bound, window = max(bulk)
    assert bulk_bound < Q('4.525092')
    # At distances >=10 past the fixed core, nine backward digits are
    # unchanged by replacement with a legal tail. q_9 >= F_10 = 55.
    far = bulk_bound + Q(1, 3025)
    theta = Q('4.525423')
    assert far < theta < TARGET[0]
    core = A[::-1] + (4,) + B
    core_bounds = []
    for i, digit in enumerate(core):
        if i == len(A):
            continue
        value = digit + rational_maximum(core[:i][::-1], A) + rational_maximum(core[i+1:], B)
        assert value < theta
        core_bounds.append({'position': i-len(A), 'upper': str(value)})
    near_max, witness, counted, compared = Q(0), None, 0, 0
    for side, near, other in [('left', A, B), ('right', B, A)]:
        frontier = [()]
        for distance in range(1, 10):
            children = []
            for ext in frontier:
                for digit in (1, 2, 3):
                    word = ext + (digit,)
                    if not legal(near + word):
                        continue
                    children.append(word)
                    counted += 1
                    if digit <= 2:
                        continue  # local value <4
                    backward = (near + ext)[::-1] + (4,) + other
                    if backward[0] >= 2:
                        continue  # local value <4.5
                    value = digit + rational_maximum(backward, other) + rational_maximum((), near + word)
                    assert value < theta
                    compared += 1
                    if value > near_max:
                        near_max, witness = value, [side, distance, ''.join(map(str, word))]
            frontier = children
    assert Q(9, 2) < theta
    # Independent rational enclosures also check the algebraic root hull.
    enclosures = []
    for w in (A, B):
        endpoints = []
        for minimize in (True, False):
            tails = rational_tail(w[-4:], minimize == (len(w) % 2 == 0))
            endpoints.append(tuple(sorted(rational_cf(w, t) for t in tails)))
        enclosures.append(endpoints)
    L, H = interval(A, B)
    for i, value in enumerate((L, H)):
        lower = enclosures[0][i][0] + enclosures[1][i][0]
        upper = enclosures[0][i][1] + enclosures[1][i][1]
        assert K(lower) <= value <= K(upper)
    return {'passed': True, 'arithmetic': 'rational only, independent CF recurrence and word checks',
            'theta_rational': str(theta), 'bulk_upper_rational': str(bulk_bound),
            'bulk_window': window, 'legal_windows': len(bulk), 'radius': 9,
            'far_bound_rational': str(far), 'enumerated_near_prefixes': counted,
            'near_comparisons': compared, 'near_upper_rational': str(near_max),
            'near_witness': witness, 'core_bounds': core_bounds}


def replay(full):
    manifest = json.loads((FREIMAN/'data/graph_wide_verification_manifest.json').read_text())
    assert manifest['passed'] and manifest['exact_input_reproduced']
    for filename, digest in manifest['sha256'].items():
        assert hashlib.sha256(artifact_path(filename).read_bytes()).hexdigest() == digest, filename
    if full:
        from certified_kernel_input import prepare
        name = HERE/'data/below_ray_kernel_input'
        prepare(str(FREIMAN/'data/graph_wide'), str(name), graph=True, tight=True)
        generated = name.with_suffix('.dat')
        assert generated.read_bytes() == (FREIMAN/'data/graph_wide.dat').read_bytes()
        binary = HERE/'bin/below_ray_kernel_verify'
        subprocess.run(['c++', '-std=c++17', '-O3', str(FREIMAN/'src/graph_kernel.cpp'), '-o', str(binary)], check=True)
        output = HERE/'data/below_ray_kernel_replay.json'
        with (HERE/'logs/below_ray_kernel_replay.log').open('w') as log:
            subprocess.run([str(binary), str(generated), str(output),
                            str(FREIMAN/'data/graph_wide.json.alive.bin')], stdout=log, check=True)
        report = json.loads(output.read_text())
        assert report['verification_only'] and report['closed_family_found']
        assert report['surviving_states'] == manifest['fixed_family_replayed'] == 3464816
        assert Path(str(output)+'.alive.bin').read_bytes() == (FREIMAN/'data/graph_wide.json.alive.bin').read_bytes()
    return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    for folder in ('bin', 'data', 'logs'):
        (HERE/folder).mkdir(exist_ok=True)
    manifest = replay(args.full)
    kernel = ReturnSearch('graph_wide')
    assert kernel.certified
    L, H = interval(A, B)
    # The 25 explicit rows tile [1/16,7/8] with overlaps of 1/32.
    rows, verified = [], []
    for typ in range(3, 28):
        p, q = Q(typ-1, 32), Q(typ+1, 32)
        iv = L+p*(H-L), L+q*(H-L)
        row = {'a': '322', 'b': '431', 'band': [str(p), str(q)],
               'interval': [v.data() for v in iv],
               'proofs': [{'kernel': 'graph_wide', 'geometry': 193, 'bin': -20,
                           'type': typ, 'band': [str(p), str(q)]}]}
        verified.append(check_row(row, {'graph_wide': kernel}))
        rows.append(row)
    joined = union(verified)
    assert joined == [(L+(H-L)/16, L+7*(H-L)/8)]
    low, high = (4+v for v in joined[0])
    assert low < TARGET[0] < TARGET[1] < high < CF
    spectral = bound_root(A, B, 4, K(Q('4.5257')))
    theta = K(*spectral['theta_upper'])
    assert theta == K(Q(1,3025), Q(4,19)) and theta < low
    independent = independent_spectral_audit()
    # Controls: a missing endpoint band must not certify the full interval.
    assert union(verified[1:])[0][0] > joined[0][0]
    assert union(verified[:-1])[-1][1] < joined[0][1]
    damaged = dict(rows[0], proofs=[dict(rows[0]['proofs'][0], bin=-19)])
    try:
        check_row(damaged, {'graph_wide': kernel})
    except AssertionError:
        pass
    else:
        raise AssertionError('Wrong scale bin accepted')
    certificate = {'schema': 'berstein_below_hall_ray_v1', 'language': '31313 forbidden in outward words; tails use 1,2,3',
                   'center': 4, 'left': '322', 'right': '431', 'rows': rows,
                   'filled_markov_interval': [low.data(), high.data()],
                   'rational_interval': [str(v) for v in TARGET],
                   'noncentral_upper': theta.data()}
    (HERE/'data/below_ray_certificate.json').write_text(json.dumps(certificate, indent=2)+'\n')
    imported = {Path(m.__file__).resolve() for m in list(sys.modules.values())
                if getattr(m, '__file__', None) and str(FREIMAN/'src') in str(m.__file__)}
    sources = imported | {Path(__file__).resolve(), FREIMAN/'src/graph_kernel.cpp',
                         FREIMAN/'src/certified_kernel_input.py', HERE/'data/below_ray_certificate.json',
                         FREIMAN/'data/graph_wide.dat', FREIMAN/'data/graph_wide.meta.json',
                         FREIMAN/'data/graph_wide.json.alive.bin'}
    report = {'passed': True, 'claim': '[4.52578,4.52754] subset M below c_F',
              'markov_interior_below_hall_ray_proved': True,
              'KF_131_sum_interior_proved': False,
              'full_kernel_replayed_this_run': args.full,
              'kernel_closed_rows': manifest['fixed_family_replayed'],
              'root_bands_verified': len(rows), 'negative_controls': 3,
              'exact_filled_interval': [low.data(), high.data()],
              'filled_interval_decimal': [float(low), float(high)],
              'rational_interval': [str(v) for v in TARGET],
              'spectral': spectral, 'independent_rational_audit': independent,
              'sha256': {str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(sources)}}
    (HERE/'data/below_ray_verified.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256','spectral','independent_rational_audit')},indent=2))


if __name__ == '__main__':
    main()
