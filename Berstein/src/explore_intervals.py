"""Search for extensions using all bands of the existing 31313 certificate.

Discovery uses floats; verify_interval_extensions.py accepts only exact fixed
rows and all-position bounds. Neither script modifies the original certificate.
"""
import argparse
import json
import sys
from itertools import product
from pathlib import Path
from fractions import Fraction as Q

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'Freiman/src'))
from exact_cf import K, CF, union, interval
from endpoint_return import ReturnSearch
from bridge_search import point_bands
from spectral_bounds import bound_root
sys.path.insert(0, str(ROOT / 'Berstein/src'))
from search_freiman_bridge import word_info, core_max
from spectral_rational import RationalBounds


def joined_bands(kernel, a, b):
    result = []
    for p,q,proof in sorted(point_bands(kernel,a,b),key=lambda v:(v[0],v[1])):
        proof = dict(proof, band=[str(p),str(q)])
        if result and p <= result[-1][1]:
            result[-1][1] = max(q,result[-1][1])
            result[-1][2].append(proof)
        else:
            result.append([p,q,[proof]])
    L,H = interval(a,b)
    return [dict(a=''.join(map(str,a)), b=''.join(map(str,b)),
                 band=[str(p),str(q)], proofs=proofs,
                 interval=[(L+p*(H-L)).data(),(L+q*(H-L)).data()])
            for p,q,proofs in result]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--length', type=int, default=6)
    p.add_argument('--threshold', default='4.52510')
    args = p.parse_args()
    kernel = ReturnSearch('graph_wide')
    kernel.name = 'graph_wide'
    assert kernel.certified
    floor = K(Q(args.threshold))
    spectral_bounds = RationalBounds([(3,1,3,1,3)], backward=8)
    words = [(d,) + w for n in range(2, args.length + 1)
             for w in product((1, 2, 3), repeat=n-1) for d in (3, 4)
             if word_info((d,) + w)]
    aa = [w for w in words if w[0] == 3]
    bb = [w for w in words if w[0] == 4]
    pool = []
    screened = 0
    for a in aa:
        la, ha, *_ = word_info(a)
        for b in bb:
            lb, hb, *_ = word_info(b)
            if 4+ha+hb < float(floor) or 4+la+lb > float(CF):
                continue
            theta = core_max(a, b, 4)
            if theta > min(4+ha+hb, float(CF)):
                continue
            screened += 1
            for row in joined_bands(kernel, a, b):
                lo, hi = (4+K(*x) for x in row['interval'])
                if max(float(lo), theta, float(floor)) < min(float(hi), float(CF)):
                    pool.append(dict(row, center=4, screen_theta=theta))
    print(json.dumps({'screened_roots': screened, 'bands': len(pool)}), flush=True)
    # Cover each connected component, computing spectral bounds only as needed.
    cache = {}
    accepted = []
    covered = []
    for row in sorted(pool, key=lambda r: K(*r['interval'][0])):
        lo, hi = (4+K(*x) for x in row['interval'])
        hi = min(hi, CF)
        lo = max(lo, floor)
        if any(l <= lo and hi <= h for l, h in covered):
            continue
        key = row['a'], row['b']
        if key not in cache:
            cache[key] = spectral_bounds.root(tuple(map(int,key[0])),
                                              tuple(map(int,key[1])),4)
        spectral = cache[key]
        theta = K(Q(spectral['theta']))
        lo = max(lo, theta)
        if lo >= hi:
            continue
        result = {k:v for k,v in row.items() if k != 'screen_theta'}
        result.update(covered_interval=[lo.data(),hi.data()],
                      theta_upper=theta.data())
        accepted.append(result)
        covered = union(covered + [(lo,hi)])
        print('ACCEPT', *key, float(lo), float(hi), 'components', len(covered), flush=True)
    report = {'schema':'berstein_interval_extension_discovery_v1',
              'scope':'Finite root search; no global maximality claim.',
              'maximum_outward_length':args.length, 'threshold':args.threshold,
              'screened_roots':screened, 'candidate_bands':len(pool),
              'rows':accepted, 'spectral_reports':list(cache.values()),
              'components':[[x.data() for x in iv] for iv in covered],
              'components_decimal':[[float(x) for x in iv] for iv in covered]}
    (ROOT/'Berstein/data/interval_extensions_candidates.json').write_text(
        json.dumps(report,indent=2)+'\n')
    print('COMPONENTS',report['components_decimal'],flush=True)


if __name__ == '__main__':
    main()
