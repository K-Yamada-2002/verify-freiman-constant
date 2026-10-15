"""Recheck 31313 root bands, compatible-past replacement, and core bounds.

Run explore_intervals.py first to discover roots. --full replays every adopted
row of the unchanged original kernel; all other checks always run exactly.
This does not extend the Lean development to the new endpoints.
"""
import argparse
import copy
import hashlib
import json
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT/'Berstein'
sys.path.insert(0,str(ROOT/'Freiman/src'))
from exact_cf import K,CF,union
from endpoint_return import ReturnSearch
from verify_hall_ray import check_row
from spectral_bounds import bulk_maximum, fibonacci
sys.path.insert(0,str(HERE/'src'))
from verify_below_ray import replay
from spectral_rational import RationalBounds
from tail_replacement import prove_root,periodic_bulk_endpoint


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--full',action='store_true')
    args = p.parse_args()
    manifest = replay(False)
    if args.full:
        binary = HERE/'bin/interval_extensions_kernel_verify'
        subprocess.run(['c++','-std=c++17','-O3',str(ROOT/'Freiman/src/graph_kernel.cpp'),
                        '-o',str(binary)],check=True)
        with (HERE/'logs/interval_extensions_kernel_replay.log').open('w') as log:
            subprocess.run([str(binary),str(ROOT/'Freiman/data/graph_wide.dat'),
                            str(HERE/'data/interval_extensions_kernel_replay.json'),
                            str(ROOT/'Freiman/data/graph_wide.json.alive.bin')],
                           stdout=log,check=True)
    replay_path = HERE/'data/interval_extensions_kernel_replay.json'
    checked = json.loads(replay_path.read_text())
    assert checked['verification_only'] and checked['closed_family_found']
    assert checked['surviving_states'] == manifest['fixed_family_replayed']
    assert Path(str(replay_path)+'.alive.bin').read_bytes() == \
        (ROOT/'Freiman/data/graph_wide.json.alive.bin').read_bytes()
    kernel = ReturnSearch('graph_wide')
    source = HERE/'data/interval_extensions_candidates.json'
    candidates = json.loads(source.read_text())
    spec = RationalBounds([(3,1,3,1,3)],backward=10)
    cache = {}
    rows = []
    ancestor_words = sorted({(r['a'],r['b']) for r in candidates['rows']},
                            key=lambda pair:(len(pair[0])+len(pair[1]),pair))
    def tail_extension(word,prefix):
        return word.startswith(prefix) and all(d in '123' for d in word[len(prefix):])
    def analyze(key):
        a,b=tuple(map(int,key[0])),tuple(map(int,key[1]))
        result=prove_root(a,b)
        result['rational_window_control']=spec.root(a,b,4)
        assert K(*result['theta_upper'])<=K(Q(result['rational_window_control']['theta']))
        return result
    for row in candidates['rows']:
        assert row['center'] == 4
        l,h = check_row(row,{'graph_wide':kernel})
        # A uniform bound for a shorter outward pair remains valid for every
        # legal extension. Recheck a small set of ancestors instead of repeating
        # the same infinite-tail analysis for many restricted descendants.
        key = next((a,b) for a,b in ancestor_words
                   if tail_extension(row['a'],a) and tail_extension(row['b'],b))
        if key not in cache:
            cache[key] = analyze(key)
        theta = K(*cache[key]['theta_upper'])
        if theta > K(*row['theta_upper']):
            key = row['a'],row['b']
            if key not in cache:
                cache[key] = analyze(key)
            theta = K(*cache[key]['theta_upper'])
        assert theta <= K(*row['theta_upper'])
        low,high = max(4+l,theta),min(4+h,CF)
        assert low<high
        rows.append(dict(row,covered_interval=[low.data(),high.data()],theta_upper=theta.data(),
                         spectral_ancestor=list(key)))
    intervals = [tuple(K(*x) for x in row['covered_interval']) for row in rows]
    components = union(intervals)
    # The periodic-block gluing lemma in INTERVAL_EXPLORATION.md applies:
    # each realizing sequence has a finite core and two 31313-free tails.
    bulk = bulk_maximum()[0]
    assert components[0][0] == bulk
    periodic_endpoint=periodic_bulk_endpoint()
    assert K(*periodic_endpoint['maximum']) == bulk
    # Compress the proof to a covering chain for each resulting component.
    selected = []
    for left,right in components:
        current = left
        while current<right:
            options = [(h,i) for i,(l,h) in enumerate(intervals) if l<=current<h]
            high,index = max(options)
            selected.append(rows[index])
            current = high
    assert union(tuple(K(*v) for v in row['covered_interval']) for row in selected) == components
    def inward_endpoint(x,lower,denominator=10**8):
        n = int(float(x)*denominator)
        while K(Q(n,denominator)) > x:
            n -= 1
        while K(Q(n+1,denominator)) <= x:
            n += 1
        if lower and K(Q(n,denominator)) < x:
            n += 1
        return Q(n,denominator)
    rational_components = [(inward_endpoint(l,True),inward_endpoint(h,False)) for l,h in components]
    rational = tuple(K(x) for x in rational_components[0])
    margin = min(K(a)-bulk for a,b in rational_components)
    assert margin > 0
    gluing_radius = next(r for r in range(5,101)
                         if K(Q(2,fibonacci(r+1)**2)) < margin/2)
    assert components[0][0] <= rational[0] < K(Q('4.52578'))
    assert K(Q('4.52754')) < rational[1] <= components[0][1] < CF
    assert len(rational_components) == len(components)
    for (l,h),(a,b) in zip(components,rational_components):
        assert l<=K(a)<K(b)<=h<CF
    corrupt = copy.deepcopy(selected[0])
    corrupt['proofs'][0]['bin'] += 1
    try:
        check_row(corrupt,{'graph_wide':kernel})
    except AssertionError:
        pass
    else:
        raise AssertionError('Incorrect bin accepted')
    # The selected endpoint rows are necessary for the exact component.
    for index in (0,len(selected)-1):
        damaged = union(tuple(K(*v) for v in row['covered_interval'])
                        for i,row in enumerate(selected) if i != index)
        assert damaged != components
    try:
        prove_root((3,2,3),(4,3,1),damage_past=True)
    except AssertionError:
        pass
    else:
        raise AssertionError('Incompatible replacement past accepted')
    certificate = dict(schema='berstein_interval_extensions_v1',language='31313',
                       center=4,rows=selected,components=[[x.data() for x in iv] for iv in components],
                       rational_interval=[str(x.a) for x in rational],
                       rational_components=[[str(x) for x in iv] for iv in rational_components],
                       tail_replacement_witnesses=list(cache.values()),
                       periodic_bulk_endpoint=periodic_endpoint,
                       analytic_basis='Closed cover, shrinking cylinders, compatible-past replacement, finite core bounds, and gluing above the bulk endpoint; the endpoint itself is periodic.')
    output = HERE/'data/interval_extensions_certificate.json'
    output.write_text(json.dumps(certificate,indent=2)+'\n')
    files = [Path(__file__).resolve(),HERE/'src/spectral_rational.py',output,source,
             ROOT/'Freiman/data/graph_wide.dat',ROOT/'Freiman/data/graph_wide.json.alive.bin',
             ROOT/'Freiman/data/graph_wide.meta.json',
             ROOT/'Freiman/src/graph_kernel.cpp',replay_path,
             HERE/'doc/INTERVAL_EXPLORATION.md']
    files = sorted(set(files) | {Path(m.__file__).resolve() for m in list(sys.modules.values())
                   if getattr(m,'__file__',None) and any(str(folder) in str(m.__file__)
                   for folder in (ROOT/'Freiman/src',HERE/'src'))})
    claim=f'[{float(rational[0]):.8f},{float(rational[1]):.8f}] subset L and M below c_F'
    report = dict(passed=True,claim=claim,
                  full_kernel_replayed_this_run=args.full,closed_rows=checked['surviving_states'],
                  candidate_rows=len(rows),certificate_rows=len(selected),
                  all_noncentral_positions_bounded=True,
                  backward_window_for_independent_control=spec.backward,
                  compatible_past_replacement=True,
                  exact_bulk_endpoint_in_L_and_M=True,
                  lagrange_inclusion_by_analytic_gluing=True,
                  bulk_upper=bulk.data(),gluing_margin=margin.data(),
                  gluing_radius=gluing_radius,
                  noncentral_bound_ancestors=[dict(a=k[0],b=k[1],theta_upper=v['theta_upper'],
                                                 core_strictly_below_bulk=v['core_strictly_below_bulk'])
                                             for k,v in cache.items()],
                  sharper_far_upper=str(spec.far()[0]),sharper_far_upper_decimal=float(spec.far()[0]),
                  components=certificate['components'],
                  components_decimal=[[float(x) for x in iv] for iv in components],
                  rational_interval=certificate['rational_interval'],
                  rational_components=certificate['rational_components'],
                  rational_width=str(rational[1].a-rational[0].a),
                  width_ratio_to_old_rational=str((rational[1].a-rational[0].a)/Q('0.00176')),
                  negative_controls=4,global_maximality_proved=False,
                  lean_proof_of_extended_endpoints=False,
                  sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files})
    (HERE/'data/interval_extensions_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256','components')},indent=2))


if __name__ == '__main__':
    main()
