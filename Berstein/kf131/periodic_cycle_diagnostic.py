#!/usr/bin/env python3
"""Separate exact ratio recurrence from scalar coverage for the two-type probe.

This is a diagnostic, not a new certificate schema or an interior proof.
"""
import argparse
import json
from pathlib import Path

from anchored_geometry import ALPHA, B, transition
from scalar_geometry import uniform_child_core
from verify_scalar_graph import ScalarVerifier
from verify_type_graph import require


def diagnose(data):
    v = ScalarVerifier(data)
    require(len(data['nodes']) == 2, 'expected the two-type periodic probe')
    require(data['nodes'][0]['parity'] == -1 and data['nodes'][1]['parity'] == 1,
            'unexpected parities')
    r, s, h = v.box(0)
    require(r == s, 'matching shape boxes required')
    require(tuple(data['nodes'][0]['states']) == tuple(data['nodes'][1]['states']),
            'matching shape states required')
    c = ALPHA**2
    require(c < h[0] < h[1] < 1, 'ratio must stay in the swapping regime')
    k = c/h[1], c/h[0]
    require((c/k[1], c/k[0]) == h, 'ratio involution failed')
    for hb, p, target in ((h, -1, k), (k, 1, h)):
        rr, ss, hh, pp = transition('2', '', r, s, hb, p)
        require(hh[0] > 1 and (1/hh[1], 1/hh[0]) == target,
                'exact ratio image failed')
        require(pp == -p and r[0] <= ss[0] <= ss[1] <= r[1]
                and s[0] <= rr[0] <= rr[1] <= s[1], 'shape/parity return failed')
    j0, j1 = (v.interval(n['interval']) for n in data['nodes'])
    require(j0[0] == -j0[1] and j1[0] == -j1[1], 'symmetric intervals required')
    core0 = uniform_child_core('2', '', True, j1, r, s, h, -1)
    core1 = uniform_child_core('2', '', True, j0, r, s, k, 1)
    require(core0 == (-h[0]*j1[1], h[0]*j1[1]), 'first scalar gain failed')
    require(core1 == (-k[0]*j0[1], k[0]*j0[1]), 'second scalar gain failed')
    gain = h[0]*k[0]
    require(gain == c*h[0]/h[1] and 0 < gain < c < 1, 'cycle gain failed')
    record = lambda values: [B.coerce(x).record() for x in values]
    return dict(status='exact parameter cycle; scalar cover remains open',
                H=record(h), K=record(k), parameter_cycle_exact=True,
                scalar_cycle_gain=gain.record(), root_core=record(core0),
                companion_core=record(core1), companion_required=record(j1),
                positive_symmetric_two_edge_cycle_impossible=True,
                physical_seed=v.seed())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    result = diagnose(json.loads(args.source.read_text()))
    result['source'] = str(args.source)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])


if __name__ == '__main__':
    main()
