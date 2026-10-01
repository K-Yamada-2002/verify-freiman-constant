"""Fixed-certificate verifier for [c_F,infinity) in both M and L.

No root search, failed-row deletion, or approximate endpoint comparison.
--full also regenerates and replays both saved closed kernels.
The infinite-ray and gluing arguments are given in HALL_RAY_PROOF.md.
"""
from layout import SRC, LOGS, artifact_path
import argparse
import hashlib
import json
import subprocess
import sys
from fractions import Fraction as Q
from exact_cf import K, CF, interval, parameters, union, matrix, cf, tail_endpoint
from endpoint_return import ReturnSearch, BASE, A, B
from anchor_boxes import anchor
from spectral_bounds import bound_root, bulk_maximum
from obstruction_probe import scan, STATES, step


def check_row(row,kernels):
    a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
    assert a and b and all(1<=d<=4 for d in a+b)
    assert scan(a) is not None and scan(b) is not None
    p,q=map(Q,row['band']);assert 0<=p<q<=1
    r,s,rho=parameters(a,b)
    # Compute the automaton state again directly from the suffix.
    states=[max((t for t in STATES if not t or w[-len(t):]==t),key=len) for w in (a,b)]
    assert states==[scan(a),scan(b)]
    xa,xb=[tail_endpoint(t,len(w)%2==0) for t,w in zip(states,(a,b))]
    z=(1+r*xa)/(1+s*xb);S=rho*z*z
    certified=[]
    for proof in row['proofs']:
        kernel=kernels[proof['kernel']]
        ids=[]
        for w,t,ratio in zip((a,b),states,(r,s)):
            key=len(t),len(w)%2,w[-kernel.memory:];sid=kernel.ids[key];ids.append(sid)
            proto=tuple(kernel.meta['prototypes'][sid]);length=max(kernel.memory,len(t))
            aa,bb,cc,dd=matrix(tuple(reversed(proto[-length:])))
            bounds=sorted((aa*x+bb)/(cc*x+dd) for x in
                          map(Q,kernel.meta.get('prehistory_interval',['0','1'])))
            assert bounds[0]<=ratio<=bounds[1]
            # Current suffix determines every next allowed digit and state.
            assert all(step(t,d)==step(scan(proto),d) for d in (1,2,3))
        ia,ib=ids
        geom=ia*kernel.sides+ib;i=proof['bin'];typ=proof['type']
        assert geom==proof['geometry'] and kernel.low<=i<=kernel.high
        assert kernel.base**i<=S<=kernel.base**(i+1)
        assert ((geom*kernel.bins+i-kernel.low)*kernel.T+typ) in kernel.alive
        expected=next((l,h) for t,l,h in kernel.bands if t==typ)
        assert tuple(map(Q,proof['band']))==expected
        certified.append(expected)
    merged=union(certified)
    assert any(l<=p and q<=h for l,h in merged)
    sides=[sorted(cf(w,tail_endpoint(t,m)) for m in (True,False)) for w,t in zip((a,b),states)]
    L,H=(sides[0][i]+sides[1][i] for i in (0,1))
    result=L+p*(H-L),L+q*(H-L)
    assert [v.data() for v in result]==row['interval']
    return result


def reaches(intervals,start,target):
    current=start
    for lo,hi in intervals:
        if lo>current or hi<=current:return False
        current=hi
    return current>=target


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--full',action='store_true')
    args=parser.parse_args()
    kernels={};manifests={}
    for name in ('graph_m2','graph_wide'):
        if args.full:
            with (LOGS/(name+'_hall_replay.log')).open('w') as log:
                subprocess.run([sys.executable,'-B',str(SRC/'verify_invariant_certificate.py'),name],
                               stdout=log,check=True)
        manifest=json.loads((BASE/(name+'_verification_manifest.json')).read_text())
        assert manifest['passed'] and manifest['exact_input_reproduced']
        for filename,digest in manifest['sha256'].items():
            assert hashlib.sha256(artifact_path(filename).read_bytes()).hexdigest()==digest,filename
        kernels[name]=ReturnSearch(name);assert kernels[name].certified
        manifests[name]=manifest['fixed_family_replayed']
    with (LOGS/'endpoint_hall_replay.log').open('w') as log:
        subprocess.run([sys.executable,'-B',str(SRC/'verify_endpoint_closure.py')],stdout=log,check=True)
    endpoint=json.loads((BASE/'endpoint_closure_verified.json').read_text())
    assert endpoint['passed'] and endpoint['endpoint_family_closed']
    data=json.loads((BASE/'hall_ray_certificate.json').read_text())
    assert data['discovery_complete']
    assert data['endpoint_source']=='endpoint_closure_verified.json'
    assert data['endpoint_interval']==endpoint['endpoint_markov_interval']
    lo,hi=(K(*v) for v in data['endpoint_interval'])
    L,H=interval(A,B)
    assert lo==CF==4+L and hi==CF+(H-L)/8
    root_bound=bound_root(A,B,4)
    assert K(*root_bound['theta_upper'])<CF
    spectral={};spectral_reports=[]
    intervals=[(lo,hi)];comparisons=0
    for row in data['finite_chain']:
        l,h=check_row(row,kernels);c=row['center'];assert c in (3,4,5)
        key=row['a'],row['b'],c
        if key not in spectral:
            result=bound_root(tuple(map(int,key[0])),tuple(map(int,key[1])),c)
            spectral[key]=K(*result['theta_upper']);spectral_reports.append(result)
        theta=spectral[key]
        assert theta.data()==row['theta_upper']
        iv=max(l+c,theta),h+c
        assert [v.data() for v in iv]==row['covered_interval']
        intervals.append(iv);comparisons+=len(row['proofs'])
    assert reaches(intervals,CF,K(Q(13,2)))
    assert intervals[-1][1].data()==data['finite_chain_end']
    assert data['translation_target']==['1/2','3/2']
    assert data['translation_centers']=='all integers >= 6'
    translated=[]
    for row in data['translation_chain']:
        assert 'center' not in row
        iv=check_row(row,kernels);translated.append(iv)
        assert [v.data() for v in iv]==row['covered_interval']
        comparisons+=len(row['proofs'])
    assert reaches(translated,K(Q(1,2)),K(Q(3,2)))
    # For central integer n>=6, all other digits are <=4, so lambda_i<6.
    # The certified template gives [n+1/2,n+3/2]; adjacent shifts meet.
    assert K(6)+K(Q(1,2))==K(Q(13,2))
    assert Q(3,2)==1+Q(1,2)
    bulk,_=bulk_maximum();assert bulk<CF
    # Every constructed sequence has two B0 tails. Gluing with 2 separators
    # gives limsup t since t>bulk; see the explicit analytic proof.
    negative={
        'missing_endpoint_rejected':not reaches(intervals[1:],CF,K(Q(13,2))),
        'missing_finite_last_row_rejected':not reaches(intervals[:-1],CF,K(Q(13,2))),
        'missing_template_last_row_rejected':not reaches(translated[:-1],K(Q(1,2)),K(Q(3,2))),
    }
    assert all(negative.values())
    source_files=['layout.py','hall_ray_certificate.json','verify_hall_ray.py','exact_cf.py','spectral_bounds.py',
                  'endpoint_return.py','anchor_boxes.py','obstruction_probe.py',
                  'box_certificates.py','typed_intervals.py','typed_boxes.py','width_catalog.py',
                  'endpoint_closure_verified.json','graph_m2_verification_manifest.json',
                  'graph_wide_verification_manifest.json']
    report={'passed':True,'claim':'[c_F,infinity) is contained in M and L',
            'proof_kind':'Exact-arithmetic computation plus the analytic iteration and gluing lemmas; not a Lean formalization.',
            'closed_kernel_states':manifests,'endpoint_family_closed':True,
            'finite_band_rows':len(data['finite_chain']),
            'distinct_finite_spectral_roots':len(spectral),
            'finite_covered_interval':[CF.data(),intervals[-1][1].data()],
            'finite_covered_interval_decimal':[float(CF),float(intervals[-1][1])],
            'translation_band_rows':len(translated),'translation_target':['1/2','3/2'],
            'translation_ray_start':'13/2','kernel_band_memberships':comparisons,
            'noncentral_bounds_recomputed':True,'tail_bulk_bound':bulk.data(),
            'gluing_margin':(CF-bulk).data(),'negative_controls':negative,
            'freiman_ray_in_M_verified':True,'freiman_ray_in_L_verified':True,
            'maximality_below_cF_proved_here':False,
            'Schecker_or_Freiman_external_tables_used':False,
            'sha256':{f:hashlib.sha256(artifact_path(f).read_bytes()).hexdigest() for f in source_files},
            'spectral_reports':spectral_reports}
    (BASE/'hall_ray_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256','spectral_reports')},indent=2))


if __name__=='__main__':main()
