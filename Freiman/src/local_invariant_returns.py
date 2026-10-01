"""Replace both digit-3 orbit families by finite local inequalities.

This is an independent additional certificate.  It does not change the old
endpoint proof.  A local condition contains only the current words' states,
parities, reversed continuant ratios r,s, and derivative ratio at
zeta=[0;overline{3}].  Neither an ancestor nor a repetition counter occurs.

The accepted endpoint menus are replayed using a conservative enclosure in
the old lower-endpoint derivative coordinate S.  The return (33,33) is proved
to preserve the local condition exactly, rather than enclosing its S image.
"""
import hashlib
import json
from fractions import Fraction as Q
from itertools import product
from math import isqrt

from anchor_boxes import anchor, derivative_fraction
from box_certificates import child_box, contains
from endpoint_certificate import certify_menu
from endpoint_return import A, B, U, V, STABLE, BASE, ReturnSearch
from exact_cf import matrix
from obstruction_probe import scan


P, H = Q(17, 100), Q(19, 100)
LOOP = (3, 3)
# These prototypes encode the local state, parity, and suffix only.  They are
# not ancestors of the admitted words.
LEFT, RIGHT = (1, 3, 3), (3, 3)
LOCAL_ROWS = {
    'R0_local': ((Q('0.3027756'), Q('0.302776')),
                 (Q('0.3027756'), Q('0.302776')),
                 (Q('8.43192'), Q('8.43194'))),
    'R1_local': ((Q('0.3027756'), Q('0.302780')),
                 (Q('0.3027756'), Q('0.302806')),
                 (Q('8.42593'), Q('8.42603'))),
}
BROAD_ROOT = ((Q('0.278688'), Q('0.278689')),
              (Q('0.410958'), Q('0.410959')),
              (Q('0.845630'), Q('0.845631')))
BROAD_ENDPOINT = STABLE[:2] + ((Q('0.845630'), Q('0.845631')),)
SOURCE_MENUS = {
    'R0_local': 'root_thirdigit_replayed.json',
    'R1_local': 'stable_thirdigit_replayed.json',
}


def zeta_enclosure():
    scale = 10 ** 40
    z = isqrt(13 * scale * scale)
    low, high = (Q(z, scale) - 3) / 2, (Q(z + 1, scale) - 3) / 2
    assert 0 < low <= high
    assert low * low + 3 * low - 1 <= 0 <= high * high + 3 * high - 1
    return low, high


def convert_scale(a, b, box, to_zeta):
    """Enclose S <-> V_zeta for independent r,s,scale intervals.

    With x=anchor(a),y=anchor(b),
      V_zeta = S ((1+r*zeta)/(1+r*x))^2
                   ((1+s*y)/(1+s*zeta))^2.
    Each positive unsquared factor is fractional linear in each coordinate
    separately, so its extrema lie at corners.  Rational bounds for zeta
    avoid changing the exact endpoint field used by the existing verifier.
    """
    x, y = anchor(a), anchor(b)
    values = []
    for r, s, z, scale in product(box[0], box[1], zeta_enclosure(), box[2]):
        factor = (1 + r * z) / (1 + r * x) * (1 + s * y) / (1 + s * z)
        assert factor > 0
        if not to_zeta:
            factor = 1 / factor
        values.append(scale * factor * factor)
    return min(values), max(values)


def induced_anchor_box(a, b, local):
    return local[:2] + (convert_scale(a, b, local, False),)


def signature_ok(a, b):
    return (scan(a) == scan(b) == (3,)
            and len(a) % 2 == 1 and len(b) % 2 == 0
            and a[-2:] == b[-2:] == LOOP)


def verify_local_return(local):
    assert signature_ok(LEFT, RIGHT)
    assert signature_ok(LEFT + LOOP, RIGHT + LOOP)
    assert matrix(LOOP) == (1, 3, 3, 10)
    # T_33(r)=(3+r)/(10+3r) is increasing.  Check both extrema.
    for low, high in local[:2]:
        f = lambda r: (3 + r) / (10 + 3 * r)
        assert low <= f(low) <= f(high) <= high
        # For continued fractions with digits in {1,2,3}, these bounds also
        # force the last two digits to be 33; this suffix need not be an
        # additional mathematical admissibility condition.
        assert Q(1, 4) < low <= high < Q(1, 3)
        assert Q(1, 4) < 1 / high - 3 <= 1 / low - 3 < Q(1, 3)
    # F_33(zeta)-zeta has numerator -3(zeta^2+3*zeta-1)=0.
    # Chain rule therefore multiplies both derivatives by |F_33'(zeta)|,
    # preserving V_zeta exactly; its interval is unchanged.
    assert local[2][0] > 0


def verify_entry(a, b, box, row, local):
    u, w = tuple(row['u']), tuple(row['w'])
    assert tuple(map(Q, row['band'])) == (P, H)
    assert signature_ok(a + u, b + w)
    rr, ss, _ = child_box(box, u, w)
    fa, fb = derivative_fraction(a, u, box[0]), derivative_fraction(b, w, box[1])
    scale = (box[2][0] * fb[0] / fa[1], box[2][1] * fb[1] / fa[0])
    vbox = convert_scale(a + u, b + w, (rr, ss, scale), True)
    assert contains(local, (rr, ss, vbox)), ('entry_outside_local_row', row)
    return {'u': list(u), 'w': list(w),
            'enclosure': [[str(x) for x in pair] for pair in (rr, ss, vbox)]}


def main():
    kernel = ReturnSearch('graph_wide')
    assert kernel.certified
    manifest_name = 'graph_wide_verification_manifest.json'
    manifest = json.loads((BASE / manifest_name).read_text())
    assert manifest['passed'] and manifest['fixed_family_replayed'] == 3464816
    for name in ('graph_wide.dat', 'graph_wide.meta.json', 'graph_wide.json.alive.bin'):
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == manifest['sha256'][name]
    result = {'passed': True, 'uses_ancestor_or_exponent': False,
              'coordinate': 'V_zeta=abs(F_b_prime(zeta))/abs(F_a_prime(zeta))',
              'zeta_equation': 'zeta^2+3*zeta-1=0; zeta>0',
              'local_signature': {'left_state': [3], 'right_state': [3],
                                  'left_parity': 1, 'right_parity': 0,
                                  'left_suffix': [3, 3], 'right_suffix': [3, 3]},
              'target': [str(P), str(H)], 'rows': []}
    for name, local in LOCAL_ROWS.items():
        verify_local_return(local)
        source = json.loads((BASE / SOURCE_MENUS[name]).read_text())
        def check_loop(row):
            assert tuple(row['u']) == tuple(row['w']) == LOOP
            assert tuple(map(Q, row['band'])) == (P, H)
            verify_local_return(local)
        certified, stats = certify_menu(kernel, LEFT, RIGHT,
                                         induced_anchor_box(LEFT, RIGHT, local),
                                         (P, H), source['menu'], check_loop)
        incoming_source = ('root_endpoint_connected.json' if name == 'R0_local'
                           else 'stable_endpoint_uniform.json')
        incoming = json.loads((BASE / incoming_source).read_text())
        a, b, box = ((A, B, BROAD_ROOT) if name == 'R0_local'
                     else (A + U, B + V, BROAD_ENDPOINT))
        entries = []
        for row in incoming['menu']:
            if row['destination'] in ('proved_root_thirdigit_chart',
                                       'proved_stable_thirdigit_chart'):
                entries.append(verify_entry(a, b, box, row, local))
        assert entries
        result['rows'].append({'name': name,
                               'local_box': [[str(x) for x in pair] for pair in local],
                               'local_return_verified': True,
                               'uniform_cover_verified': True,
                               'menu_source': SOURCE_MENUS[name],
                               'menu_size': len(certified),
                               'menu': certified, 'incoming_verified': entries,
                               **stats})
    result['statement'] = ('For every pair of current words satisfying either local row, '
                           'J_[17/100,19/100] is covered by listed kernel intervals and '
                           'its (33,33) successor, which satisfies the same local row.')
    result['scope'] = 'Digit-3 returns only; the endpoint and general kernel definitions are unchanged.'
    result['sha256'] = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                        for name in (manifest_name, *SOURCE_MENUS.values(),
                                     'root_endpoint_connected.json', 'stable_endpoint_uniform.json')}
    output = BASE / 'local_invariant_returns_verified.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('rows', 'sha256')}, indent=2))
    for row in result['rows']:
        print(json.dumps({k: v for k, v in row.items() if k not in ('menu', 'incoming_verified')}, indent=2))


if __name__ == '__main__':
    main()
