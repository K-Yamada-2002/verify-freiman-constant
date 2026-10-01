"""Replay the closed endpoint lemma, including all special-family transitions.

No searching or deletion of failed rows is performed. An assertion failure
means the supplied endpoint certificate is not verified.
"""
from layout import artifact_path
import hashlib
import json
from fractions import Fraction as Q
from itertools import product

from endpoint_return import ReturnSearch, A, B, U, V, STABLE, S0, r0, s0, BASE
from adaptive_return_chart import thirdigit_family_box
from endpoint_certificate import certify_menu
from anchor_boxes import anchor, derivative_fraction, AnchorUniform
from typed_intervals import E, cf
from box_certificates import child_box, contains
from obstruction_probe import scan
from exact_cf import CF, K, interval

DELTA = Q(1, 8)
P, QTOP = Q(17, 100), Q(19, 100)
UA, WB = (1, 3, 1, 2), (3, 1)
ROOT_BOX = ((r0, r0), (s0, s0), (S0, S0))


def main():
    kernel = ReturnSearch('graph_wide')
    assert kernel.certified
    manifest = json.loads((BASE / 'graph_wide_verification_manifest.json').read_text())
    assert manifest['passed'] and manifest['fixed_family_replayed'] == 3464816
    for filename in ('graph_wide.dat', 'graph_wide.meta.json', 'graph_wide.json.alive.bin'):
        assert hashlib.sha256((BASE / filename).read_bytes()).hexdigest() == manifest['sha256'][filename]
    assert S0 > 0
    assert S0 == E.quad(Q(2941188465121, 6906504888529), Q(134881150564, 6906504888529), 462)
    # The paired extremal periods preserve the actual lower endpoint and S.
    gamma = E.quad(3697, -172, 462)
    assert 0 < gamma < 1
    for a, b, box in ((A, B, ROOT_BOX), (A + U, B + V, STABLE)):
        assert cf(U, anchor(a + U)) == anchor(a)
        assert cf(V, anchor(b + V)) == anchor(b)
        assert derivative_fraction(a, U, box[0]) == (gamma, gamma)
        assert derivative_fraction(b, V, box[1]) == (gamma, gamma)
        rr, ss, _ = child_box(box, U, V)
        assert contains(STABLE[:2], (rr, ss))
        assert scan(a + U) == scan(A + U) and scan(b + V) == scan(B + V)
        assert (len(a + U) % 2, len(b + V) % 2) == (1, 0)
        assert (a + U)[-2:] == (1, 3) and (b + V)[-2:] == (2, 1)

    cases = [
        ('R0', 'root_thirdigit_replayed.json',
         thirdigit_family_box(A, B, ROOT_BOX, UA, WB, 6), (P, QTOP)),
        ('R1', 'stable_thirdigit_replayed.json',
         thirdigit_family_box(A + U, B + V, STABLE, UA, WB, 4), (P, QTOP)),
        ('E', 'stable_endpoint_uniform.json', (A + U, B + V, STABLE), (Q(0), DELTA)),
        ('root', 'root_endpoint_connected.json', (A, B, ROOT_BOX), (Q(0), DELTA)),
    ]
    # Cross-check the new t-coordinate formula against direct continuation
    # matrices. The proof for all exponents uses the invariant t interval;
    # these are implementation controls, not a finite replacement for it.
    orbit_cross_checks = 0
    for a, b, parent, minimum in ((A, B, ROOT_BOX, 6), (A + U, B + V, STABLE, 4)):
        _, _, enclosure = thirdigit_family_box(a, b, parent, UA, WB, minimum)
        for r, s in set(product(parent[0], parent[1])):
            point = ((r, r), (s, s), (S0, S0))
            for exponent in (minimum, minimum + 2, minimum + 6, minimum + 14):
                u, w = UA + (3,) * exponent, WB + (3,) * exponent
                rr, ss, _ = child_box(point, u, w)
                fa, fb = derivative_fraction(a, u, point[0]), derivative_fraction(b, w, point[1])
                assert fa[0] == fa[1] and fb[0] == fb[1]
                scale = S0 * fb[0] / fa[0]
                assert contains(enclosure, (rr, ss, (scale, scale)))
                orbit_cross_checks += 1
    reports = []
    verified_menus = {}
    negative_controls = []
    for label, filename, (a, b, box), target in cases:
        data = json.loads((BASE / filename).read_text())
        assert data.get('verified') or data.get('local_cover')
        assert tuple(map(Q, data['target'])) == target
        def special(row):
            u, w = tuple(row['u']), tuple(row['w'])
            band = tuple(map(Q, row['band']))
            if label in ('R0', 'R1'):
                # The state retains the ancestor and exponent. Appending 33
                # increments the even exponent by 2, with the ancestor fixed.
                assert u == w == (3, 3) and band == (P, QTOP)
                assert row['destination'] in ('same_orbit_family', 'same_nested_orbit_family')
            elif row['destination'] in ('endpoint_state', 'same_endpoint_state'):
                assert u == U and w == V and band == (Q(0), DELTA)
            else:
                assert band == (P, QTOP)
                assert u[:len(UA)] == UA and w[:len(WB)] == WB
                uu, ww = u[len(UA):], w[len(WB):]
                assert uu == ww and all(d == 3 for d in uu) and len(uu) % 2 == 0
                if label == 'root':
                    assert row['destination'] == 'proved_root_thirdigit_chart' and len(uu) >= 6
                else:
                    assert row['destination'] == 'proved_stable_thirdigit_chart' and len(uu) >= 4
        rows, statistics = certify_menu(kernel, a, b, box, target, data['menu'], special)
        report = {'state': label, 'source': filename, 'menu_size': len(rows),
                  'maximum_added_length': max(len(v['u']) + len(v['w']) for v in rows),
                  'special_returns': [v for v in rows if v['destination'] != 'kernel'],
                  **statistics}
        reports.append(report)
        verified_menus[label] = rows
        if label in ('E', 'R1'):
            proof = AnchorUniform(a, b, f'band_{target[0]}_{1-target[1]}', box)
            for destination in sorted({v['destination'] for v in rows if v['destination'] != 'kernel'}):
                damaged = []
                for row in rows:
                    if row['destination'] == destination:
                        continue
                    l, h = map(Q, row['band'])
                    damaged.append((tuple(row['u']), tuple(row['w']), f'band_{l}_{1-h}'))
                assert not proof.verify(damaged)
                negative_controls.append({'state': label, 'removed': destination, 'rejected': True})

    # The analytic argument is nested-cylinder iteration in the union of the
    # old kernel and these modes. Ratios are bounded and every nonterminal
    # transition extends a word, so both words grow without bound.
    L, H = interval(A, B)
    assert 4 + L == CF
    spectral = json.loads((BASE / 'spectral_I7.json').read_text())
    theta = K(*map(Q, spectral['theta_upper']))
    assert theta == K(Q(1, 441), Q(4, 19)) and theta < CF
    endpoint_interval = CF, CF + DELTA * (H - L)
    # The previous certified root band overlaps this endpoint interval.
    kernel_root = json.loads((BASE / 'graph_m2_algebraic_replay.json').read_text())
    assert kernel_root['passed'] and kernel_root['root_surviving_bands'] == [['1/16', '31/32']]
    assert DELTA >= Q(1, 16)
    full_root_band = CF, CF + Q(31, 32) * (H - L)
    old_components = json.loads((BASE / 'invariant_root_intervals.json').read_text())['components']
    first_lo, first_hi = (K(*map(Q, z)) for z in old_components[0])
    assert first_lo <= endpoint_interval[1] and first_lo == full_root_band[0] + Q(1, 16) * (H - L)
    completed_components = [[CF.data(), first_hi.data()]] + old_components[1:]
    sources = [x[1] for x in cases] + ['layout.py', 'verify_endpoint_closure.py', 'endpoint_certificate.py',
               'adaptive_return_chart.py', 'anchor_boxes.py', 'endpoint_return.py',
               'spectral_I7.json', 'graph_wide_verification_manifest.json',
               'graph_m2_algebraic_replay.json', 'invariant_root_intervals.json']
    out = {
        'passed': True, 'endpoint_family_closed': True,
        'kernel_states': manifest['fixed_family_replayed'], 'new_modes': reports,
        'root_endpoint_band': ['0', '1/8'],
        'endpoint_markov_interval': [z.data() for z in endpoint_interval],
        'endpoint_markov_interval_decimal': [float(z) for z in endpoint_interval],
        'merged_root_markov_interval': [z.data() for z in full_root_band],
        'connected_initial_markov_interval': [CF.data(), first_hi.data()],
        'connected_initial_markov_interval_decimal': [float(CF), float(first_hi)],
        'certified_markov_components': completed_components,
        'noncentral_bound': theta.data(), 'noncentral_bound_strictly_below_cF': True,
        'negative_controls': negative_controls,
        'orbit_formula_cross_checks': orbit_cross_checks,
        'freiman_ray_proved': False,
        'sha256': {f: hashlib.sha256(artifact_path(f).read_bytes()).hexdigest() for f in sources},
        'verified_menus': verified_menus,
    }
    (BASE / 'endpoint_closure_verified.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k not in ('sha256', 'verified_menus')}, indent=2))


if __name__ == '__main__':
    main()
