"""Replay finite Hall entrances and chains using graph_wide alone.

The endpoint band is a separate already verified input.  This verifier proves
that graph_m2 is unnecessary for either finite Hall chain or translation chain.
It never runs discovery or changes the original proof artifacts.
"""
import hashlib
import json
from fractions import Fraction as Q

from layout import DATA, artifact_path
from exact_cf import K, CF, interval, union
from endpoint_return import ReturnSearch, A, B
from spectral_bounds import bound_root, bulk_maximum
from verify_hall_ray import check_row, reaches


def parent_interval(a, b, band):
    l, h = interval(tuple(map(int, a)), tuple(map(int, b)))
    p, q = map(Q, band)
    assert 0 <= p < q <= 1
    return l+p*(h-l), l+q*(h-l)


def main():
    kernel = ReturnSearch('graph_wide')
    assert kernel.certified
    kernels = {'graph_wide': kernel}
    manifest = json.loads((DATA/'graph_wide_verification_manifest.json').read_text())
    assert manifest['passed'] and manifest['exact_input_reproduced']
    for name, digest in manifest['sha256'].items():
        assert hashlib.sha256(artifact_path(name).read_bytes()).hexdigest() == digest, name
    source = json.loads((DATA/'hall_ray_certificate.json').read_text())
    data = json.loads((DATA/'wide_bootstrap_certificate.json').read_text())
    assert source['discovery_complete'] and data['all_bootstraps_covered']
    entries = {}
    child_count = 0
    extended_children = 0
    for row in data['results']:
        key = row['a'], row['b'], tuple(row['band'])
        assert key not in entries
        a, b = (tuple(map(int, word)) for word in key[:2])
        l, h = parent_interval(*key)
        assert [l.data(), h.data()] == row['interval']
        certified = []
        for child in row['menu']:
            u, w = tuple(child['u']), tuple(child['w'])
            assert all(d in (1, 2, 3) for d in u+w)
            assert tuple(map(int, child['a'])) == a+u
            assert tuple(map(int, child['b'])) == b+w
            assert child['proofs'] and all(p['kernel'] == 'graph_wide' for p in child['proofs'])
            certified.append(check_row(child, kernels))
            child_count += 1
            extended_children += bool(u or w)
        assert any(lo <= l and h <= hi for lo, hi in union(certified))
        for chain, i in row['source_rows']:
            original = source[chain][i]
            assert (original['a'], original['b'], tuple(original['band'])) == key
        entries[key] = (l, h)

    direct = bootstrap = 0
    def admit(row):
        nonlocal direct, bootstrap
        key = row['a'], row['b'], tuple(row['band'])
        filtered = {**row, 'proofs': [p for p in row['proofs'] if p['kernel'] == 'graph_wide']}
        try:
            result = check_row(filtered, kernels)
            direct += 1
        except AssertionError:
            assert key in entries
            result = entries[key]
            bootstrap += 1
        assert [v.data() for v in result] == row['interval']
        return result

    endpoint = json.loads((DATA/'endpoint_closure_verified.json').read_text())
    assert endpoint['passed'] and endpoint['endpoint_family_closed']
    assert source['endpoint_interval'] == endpoint['endpoint_markov_interval']
    low, high = (K(*v) for v in source['endpoint_interval'])
    l0, h0 = interval(A, B)
    assert low == CF == 4+l0 and high == CF+(h0-l0)/8
    assert K(*bound_root(A, B, 4)['theta_upper']) < CF
    finite = [(low, high)]
    spectral = {}
    for row in source['finite_chain']:
        l, h = admit(row)
        key = row['a'], row['b'], row['center']
        assert key[2] in (3, 4, 5)
        if key not in spectral:
            result = bound_root(tuple(map(int, key[0])), tuple(map(int, key[1])), key[2])
            spectral[key] = K(*result['theta_upper'])
        assert spectral[key].data() == row['theta_upper']
        result = max(l+key[2], spectral[key]), h+key[2]
        assert [v.data() for v in result] == row['covered_interval']
        finite.append(result)
    assert reaches(finite, CF, K(Q(13, 2)))
    translated = [admit(row) for row in source['translation_chain']]
    assert reaches(translated, K(Q(1, 2)), K(Q(3, 2)))
    assert source['translation_centers'] == 'all integers >= 6'
    bulk, _ = bulk_maximum()
    assert bulk < CF
    report = {
        'passed': True,
        'claim': 'The saved finite and translation Hall chains need graph_wide only.',
        'endpoint_status': 'Separate existing endpoint certificate assumed; its band and root bound checked here.',
        'kernel': 'graph_wide',
        'kernel_states': manifest['fixed_family_replayed'],
        'fixed_entrance_conditions': len(entries),
        'fixed_entrance_child_bands': child_count,
        'children_with_nonempty_extension': extended_children,
        'direct_hall_rows': direct,
        'hall_rows_replaced_by_entrances': bootstrap,
        'finite_hall_rows': len(source['finite_chain']),
        'translation_hall_rows': len(source['translation_chain']),
        'finite_chain_covered': True,
        'translation_chain_covered': True,
        'spectral_roots_recomputed': len(spectral),
        'bulk_bound': bulk.data(),
        'graph_m2_used_for_chains': False,
        'sha256': {name: hashlib.sha256(artifact_path(name).read_bytes()).hexdigest()
                   for name in ('hall_ray_certificate.json', 'wide_bootstrap_certificate.json',
                                'wide_bootstrap_search.py', 'wide_bootstrap_verify.py',
                                'graph_wide_verification_manifest.json', 'endpoint_closure_verified.json')},
    }
    (DATA/'wide_bootstrap_verified.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
