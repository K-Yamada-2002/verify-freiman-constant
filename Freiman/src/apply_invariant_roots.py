"""Apply the closed band lemma to roots with verified spectral domination."""
import argparse
import json
from fractions import Fraction as Q

from endpoint_return import ReturnSearch, BASE
from anchor_boxes import anchor
from box_certificates import contains, suffix_range
from exact_cf import K, CF, interval, parameters
from obstruction_probe import scan


def apply(name):
    kernel = ReturnSearch(name)
    assert kernel.certified
    roots = json.loads((BASE / 'augmented_roots.json').read_text())['selected_roots']
    pieces = []
    records = []
    for root in roots:
        a, b = tuple(map(int, root['a'])), tuple(map(int, root['b']))
        center = root['center']
        r, s, rho = parameters(a, b)
        z = (1 + r * anchor(a)) / (1 + s * anchor(b))
        S = rho * z * z
        i = kernel.index(S)
        keys = [(len(scan(word)), len(word) % 2, word[-kernel.memory:]) for word in (a, b)]
        record = {'a': root['a'], 'b': root['b'], 'center': center, 'intervals': []}
        records.append(record)
        if any(key not in kernel.ids for key in keys) or not kernel.low <= i <= kernel.high:
            record['status'] = 'outside_saved_state_space'
            continue
        assert kernel.base ** i <= S <= kernel.base ** (i + 1)
        try:
            kernel.side(a, (), (r, r))
            kernel.side(b, (), (s, s))
        except AssertionError:
            record['status'] = 'outside_parameter_boxes'
            continue
        g = kernel.ids[keys[0]] * kernel.sides + kernel.ids[keys[1]]
        L, H = interval(a, b)
        theta = K(*map(Q, root['theta_upper']))
        for typ, p, q in kernel.bands:
            if ((g * kernel.bins + i - kernel.low) * kernel.T + typ) not in kernel.alive:
                continue
            lo, hi = max(CF, theta, center + L + p * (H - L)), center + L + q * (H - L)
            if lo > hi:
                continue
            record['intervals'].append([lo.data(), hi.data()])
            pieces.append((lo, hi))
        record['status'] = 'certified_nonempty_bands' if record['intervals'] else 'no_saved_band'
    merged = []
    for lo, hi in sorted(pieces):
        if merged and lo <= merged[-1][1]:
            merged[-1] = merged[-1][0], max(merged[-1][1], hi)
        else:
            merged.append((lo, hi))
    return {'closed_kernel': name, 'spectral_bounds_source': 'augmented_roots.json',
            'claim': 'These closed intervals are contained in M by the closed lemma and all-position spectral bounds.',
            'records': records, 'components': [[lo.data(), hi.data()] for lo, hi in merged],
            'components_decimal': [[float(lo), float(hi)] for lo, hi in merged],
            'includes_freiman_endpoint': bool(merged and merged[0][0] == CF),
            'freiman_ray_proved': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--kernel', default='graph_m2')
    parser.add_argument('--output', default='invariant_root_intervals.json')
    args = parser.parse_args()
    result = apply(args.kernel)
    (BASE / args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))
