"""Fixed replay of the redesigned single-kernel, local-admissibility proof.

All interval objects are J_[p,q](a,b).  The four local conditions contain
only current word signatures and rational bounds on r,s,S or V_zeta.
No ancestor, repetition count, exact S=S_* constraint, or graph_m2 data is
used.  --full regenerates and replays the one remaining general kernel.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from fractions import Fraction as Q

from layout import DATA, SRC, LOGS, artifact_path
from exact_cf import K, CF, interval, union, parameters
from endpoint_return import A, B, U, V, ReturnSearch, S0, r0, s0
from anchor_boxes import anchor, derivative_fraction, AnchorUniform
from box_certificates import child_box, contains
from endpoint_certificate import certify_menu
from local_invariant_returns import (LEFT, RIGHT, induced_anchor_box,
                                     verify_local_return, verify_entry)
from obstruction_probe import scan
from spectral_bounds import bound_root, bulk_maximum
from typed_intervals import E, cf
from verify_hall_ray import check_row, reaches


def read_box(row):
    return tuple(tuple(map(Q, pair)) for pair in row['box'])


def signature(word, state, parity, suffix):
    assert scan(word) == tuple(state)
    assert len(word) % 2 == parity
    assert word[-len(suffix):] == tuple(suffix)


def verify_local_conditions(kernel, conditions):
    assert set(conditions) == {'entry', 'period', 'three_a', 'three_b'}
    prototypes = {'entry': (A, B), 'period': (A+U, B+V),
                  'three_a': (LEFT, RIGHT), 'three_b': (LEFT, RIGHT)}
    boxes = {name: read_box(row) for name, row in conditions.items()}
    reports, negative = [], []
    gamma = E.quad(3697, -172, 462)
    assert 0 < gamma < 1
    for name, row in conditions.items():
        a, b = prototypes[name]
        signature(a, row['left_state'], row['left_parity'], row['left_suffix'])
        signature(b, row['right_state'], row['right_parity'], row['right_suffix'])
        target = tuple(map(Q, row['band']))
        box = boxes[name]
        assert all(0 < lo <= hi for lo, hi in box)
        if name in ('three_a', 'three_b'):
            assert row['coordinate'] == 'V' and target == (Q(17,100), Q(19,100))
            verify_local_return(box)
            enclosing_box = induced_anchor_box(a, b, box)
        else:
            assert row['coordinate'] == 'S' and target == (Q(0), Q(1,8))
            enclosing_box = box

        def local_destination(child):
            u, w = tuple(child['u']), tuple(child['w'])
            band = tuple(map(Q, child['band']))
            destination = child['destination']
            assert destination in conditions
            if destination == 'period':
                assert name in ('entry', 'period') and u == U and w == V
                assert band == (Q(0), Q(1,8))
                assert cf(U, anchor(a+U)) == anchor(a)
                assert cf(V, anchor(b+V)) == anchor(b)
                assert derivative_fraction(a, U, box[0]) == (gamma, gamma)
                assert derivative_fraction(b, V, box[1]) == (gamma, gamma)
                rr, ss, _ = child_box(box, U, V)
                # The common derivative multiplier cancels identically.
                assert contains(boxes['period'], (rr, ss, box[2]))
            elif name in ('entry', 'period'):
                assert destination == ('three_a' if name == 'entry' else 'three_b')
                verify_entry(a, b, box, child, boxes[destination])
            else:
                assert destination == name and u == w == (3,3)
                assert band == target
                verify_local_return(box)
            dest = conditions[destination]
            signature(a+u, dest['left_state'], dest['left_parity'], dest['left_suffix'])
            signature(b+w, dest['right_state'], dest['right_parity'], dest['right_suffix'])

        translated = [dict(child, destination=('kernel' if child['destination'] == 'general'
                                              else child['destination']))
                      for child in row['menu']]
        verified, statistics = certify_menu(kernel, a, b, enclosing_box,
                                              target, translated, local_destination)
        reports.append({'condition': name, 'menu_size': len(verified),
                        'coordinate': row['coordinate'], 'box': row['box'],
                        **statistics})
        if name in ('entry', 'period', 'three_b'):
            proof = AnchorUniform(a, b, f'band_{target[0]}_{1-target[1]}', enclosing_box)
            destinations = {'period'} if name == 'entry' else (
                {'period', 'three_b'} if name == 'period' else {'three_b'})
            for destination in destinations:
                damaged = [(tuple(v['u']), tuple(v['w']),
                            f'band_{Q(v["band"][0])}_{1-Q(v["band"][1])}')
                           for v in row['menu'] if v['destination'] != destination]
                assert not proof.verify(damaged)
                negative.append({'condition': name, 'removed': destination, 'rejected': True})
    assert contains(boxes['entry'], ((r0,r0), (s0,s0), (S0,S0)))
    return reports, negative


def verify_entrances(data, kernel):
    results, children = [], 0
    for row in data:
        a, b = (tuple(map(int, row[k])) for k in ('a', 'b'))
        assert scan(a) is not None and scan(b) is not None
        assert all(1 <= d <= 4 for d in a+b)
        p, q = map(Q, row['band'])
        assert 0 <= p < q <= 1
        low, high = interval(a,b)
        parent = low+p*(high-low), low+q*(high-low)
        assert [v.data() for v in parent] == row['interval']
        covered = []
        for child in row['menu']:
            u, w = tuple(child['u']), tuple(child['w'])
            assert u or w
            assert all(d in (1,2,3) for d in u+w)
            assert tuple(map(int, child['a'])) == a+u
            assert tuple(map(int, child['b'])) == b+w
            assert child['proofs'] and all(v['kernel'] == 'graph_wide' for v in child['proofs'])
            covered.append(check_row(child, {'graph_wide': kernel}))
            children += 1
        assert any(low <= parent[0] and parent[1] <= high for low, high in union(covered))
        results.append(parent)
    return results, children


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    if args.full:
        with (LOGS / 'unified_general_replay.log').open('w') as log:
            subprocess.run([sys.executable, '-B', str(SRC/'verify_invariant_certificate.py'),
                            'graph_wide'], stdout=log, check=True)
    manifest = json.loads((DATA/'graph_wide_verification_manifest.json').read_text())
    assert manifest['passed'] and manifest['exact_input_reproduced']
    for filename, digest in manifest['sha256'].items():
        assert hashlib.sha256(artifact_path(filename).read_bytes()).hexdigest() == digest, filename
    kernel = ReturnSearch('graph_wide')
    assert kernel.certified
    data = json.loads((DATA/'unified_proof_certificate.json').read_text())
    assert data['schema'] == 'freiman_unified_local_admissibility_v1'
    assert data['kernel'] == 'graph_wide'
    conditions = {row['name']: row for row in data['local_conditions']}
    local, negative = verify_local_conditions(kernel, conditions)
    entrances, children = verify_entrances(data['initial_entrances'], kernel)
    direct = uses = 0
    def admit(row):
        nonlocal direct, uses
        if 'entrance' in row:
            n = row['entrance']
            entry = data['initial_entrances'][n]
            assert all(row[k] == entry[k] for k in ('a','b','band','interval'))
            result = entrances[n]
            uses += 1
        else:
            assert row['proofs'] and all(v['kernel'] == 'graph_wide' for v in row['proofs'])
            result = check_row(row, {'graph_wide': kernel})
            direct += 1
        assert [v.data() for v in result] == row['interval']
        return result
    low, high = (K(*v) for v in data['endpoint_interval'])
    l0, h0 = interval(A,B)
    assert low == CF == 4+l0 and high == CF+(h0-l0)/8
    assert K(*bound_root(A,B,4)['theta_upper']) < CF
    finite, spectral = [(low,high)], {}
    for row in data['finite_chain']:
        l,h = admit(row)
        key = row['a'], row['b'], row['center']
        assert key[2] in (3,4,5)
        if key not in spectral:
            spectral[key] = K(*bound_root(tuple(map(int,key[0])),
                                          tuple(map(int,key[1])),key[2])['theta_upper'])
        assert spectral[key].data() == row['theta_upper']
        covered = max(l+key[2],spectral[key]), h+key[2]
        assert [v.data() for v in covered] == row['covered_interval']
        finite.append(covered)
    assert reaches(finite,CF,K(Q(13,2)))
    translated = [admit(row) for row in data['translation_chain']]
    assert data['translation_target'] == ['1/2','3/2']
    assert data['translation_centers'] == 'all integers >= 6'
    assert reaches(translated,K(Q(1,2)),K(Q(3,2)))
    bulk,_ = bulk_maximum()
    assert bulk < CF
    assert not reaches(finite[1:],CF,K(Q(13,2)))
    assert not reaches(finite[:-1],CF,K(Q(13,2)))
    assert not reaches(translated[:-1],K(Q(1,2)),K(Q(3,2)))
    sources = ['unified_proof_certificate.json','verify_unified_proof.py',
               'local_invariant_returns.py','graph_wide_verification_manifest.json',
               'endpoint_return.py','endpoint_certificate.py','anchor_boxes.py',
               'box_certificates.py','exact_cf.py','typed_intervals.py',
               'typed_boxes.py','spectral_bounds.py','obstruction_probe.py',
               'verify_hall_ray.py','layout.py']
    report = {'passed': True, 'claim': '[c_F,infinity) is contained in M and L',
              'proof_kind': 'Exact finite verification plus nested-cylinder iteration and gluing.',
              'general_kernels': 1, 'general_kernel': 'graph_wide',
              'general_kernel_states': manifest['fixed_family_replayed'],
              'graph_m2_data_used': False, 'ancestor_or_repetition_counter_used': False,
              'exact_endpoint_scale_equality_required': False,
              'local_conditions': local, 'local_menu_count': sum(r['menu_size'] for r in local),
              'initial_entrances': len(entrances), 'entrance_child_bands': children,
              'direct_initial_rows': direct, 'initial_rows_using_entrances': uses,
              'finite_hall_rows': len(data['finite_chain']),
              'translation_hall_rows': len(data['translation_chain']),
              'finite_covered_interval_decimal': [float(CF),float(finite[-1][1])],
              'translation_ray_start': '13/2', 'spectral_roots_recomputed': len(spectral),
              'bulk_bound': bulk.data(), 'negative_local_controls': negative,
              'negative_ray_controls_passed': True,
              'freiman_ray_in_M_verified': True, 'freiman_ray_in_L_verified': True,
              'general_conditions_under_1000_achieved': False,
              'sha256': {f: hashlib.sha256(artifact_path(f).read_bytes()).hexdigest()
                         for f in sources}}
    (DATA/'unified_proof_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'sha256'},indent=2))


if __name__ == '__main__':
    main()
