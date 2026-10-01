"""Package the redesigned proof without graph_m2 or orbit ancestry.

This is deterministic packaging of fixed menus, not a proof.  The separate
verify_unified_proof.py validates every local implication and Hall chain.
"""
import json
from layout import DATA
from local_invariant_returns import BROAD_ROOT, BROAD_ENDPOINT, LOCAL_ROWS


def box_data(box):
    return [[str(x) for x in pair] for pair in box]


def main():
    specifications = [
        ('entry', 'root_endpoint_connected.json', BROAD_ROOT, 'S',
         [3], [], [1, 3], [2, 2], ['0', '1/8']),
        ('period', 'stable_endpoint_uniform.json', BROAD_ENDPOINT, 'S',
         [3], [], [1, 3], [2, 1], ['0', '1/8']),
        ('three_a', 'root_thirdigit_replayed.json', LOCAL_ROWS['R0_local'], 'V',
         [3], [3], [3, 3], [3, 3], ['17/100', '19/100']),
        ('three_b', 'stable_thirdigit_replayed.json', LOCAL_ROWS['R1_local'], 'V',
         [3], [3], [3, 3], [3, 3], ['17/100', '19/100']),
    ]
    conditions = []
    for name, filename, box, coordinate, sa, sb, va, vb, band in specifications:
        source = json.loads((DATA / filename).read_text())
        menu = []
        for row in source['menu']:
            if row['destination'] == 'kernel':
                destination = 'general'
            elif name in ('three_a', 'three_b'):
                destination = name
            elif 'endpoint_state' in row['destination']:
                destination = 'period'
            else:
                destination = 'three_a' if name == 'entry' else 'three_b'
            menu.append({k: row[k] for k in ('u', 'w', 'band')} |
                        {'destination': destination})
        conditions.append({'name': name, 'coordinate': coordinate,
                           'left_state': sa, 'right_state': sb,
                           'left_parity': 1, 'right_parity': 0,
                           'left_suffix': va, 'right_suffix': vb,
                           'box': box_data(box), 'band': band, 'menu': menu})
    old = json.loads((DATA / 'hall_ray_certificate.json').read_text())
    entrances = json.loads((DATA / 'wide_bootstrap_certificate.json').read_text())
    assert entrances['all_bootstraps_covered']
    fixed = []
    lookup = {}
    for i, row in enumerate(entrances['results']):
        key = row['a'], row['b'], tuple(row['band'])
        assert key not in lookup
        lookup[key] = i
        fixed.append({k: row[k] for k in ('a', 'b', 'band', 'interval', 'menu')})
    result = {'schema': 'freiman_unified_local_admissibility_v1',
              'kernel': 'graph_wide', 'local_conditions': conditions,
              'initial_entrances': fixed,
              'endpoint_interval': old['endpoint_interval'],
              'translation_target': old['translation_target'],
              'translation_centers': old['translation_centers']}
    for chain in ('finite_chain', 'translation_chain'):
        result[chain] = []
        for original in old[chain]:
            row = {k: v for k, v in original.items() if k != 'proofs'}
            key = row['a'], row['b'], tuple(row['band'])
            if key in lookup:
                row['entrance'] = lookup[key]
            else:
                row['proofs'] = [p for p in original['proofs']
                                 if p['kernel'] == 'graph_wide']
                assert row['proofs']
            result[chain].append(row)
    (DATA / 'unified_proof_certificate.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps({'local_conditions': len(conditions),
                      'initial_entrances': len(fixed),
                      'general_kernels': 1, 'proof_not_yet_verified': True}))


if __name__ == '__main__':
    main()
