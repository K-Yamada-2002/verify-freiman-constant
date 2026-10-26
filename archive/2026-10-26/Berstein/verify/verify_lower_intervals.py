"""Exact fixed-root verification for the 31313,13131 closed family.

Uses two full fixed-family replays, independent input semantics, rational core
and interface bounds, and the analytic closed-cover and gluing lemmas.
This is not a Lean formalization of the new language.
"""
import hashlib
import json
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
from field import E
from prepare_313 import matrix,cf,scan,tail_endpoint
from search_313_intervals import Table,union
from compatible_past import prove
from spectral_rational import RationalBounds

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'Berstein/data'
NAME='avoid_alt5_spine10'
BAD=[(3,1,3,1,3),(1,3,1,3,1)]


def main():
    table=Table(NAME)
    assert table.meta['language']=='31313,13131' and table.meta['radicand']==41667
    replay=json.loads((DATA/(NAME+'_replay.json')).read_text())
    independent=json.loads((ROOT/'Berstein/logs'/f'{NAME}_independent.log').read_text().splitlines()[-1])
    assert replay['verification_only'] and replay['closed_family_found']
    assert replay['surviving_states']==independent['adopted_rows']==4260954
    assert independent['passed'] and independent['failed_cells']==0
    assert table.bits==(DATA/(NAME+'_replay.json.alive.bin')).read_bytes()
    audit_path=DATA/(NAME+'_input_audit.json')
    audit=json.loads(audit_path.read_text());assert audit['passed']
    for path,digest in audit['sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
    bulk=E.quad(0,Q(4,181),41667)
    # Recompute the bilateral maximum from all legal five-letter windows.
    from itertools import product
    def maximum(w,state):return cf(w,tail_endpoint(state,len(w)%2==1))
    values=[w[2]+maximum(w[:2][::-1],scan(w[::-1]))+maximum(w[3:],scan(w))
            for w in product((1,2,3),repeat=5) if scan(w) is not None]
    assert max(values)==bulk
    source=DATA/(NAME+'_candidates.json')
    discovered=json.loads(source.read_text())
    upper=Q(discovered['target_window'][1])
    spec=RationalBounds(BAD,backward=8)
    cache={};rows=[]
    fields=('a','b','band','types','geometry','bin','interval')
    def check_row(row):
        assert row['a'] and row['b'] and all(d in '1234' for d in row['a']+row['b'])
        a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        assert any(all(row[k]==candidate[k] for k in fields) for candidate in table.rows(a,b))
    for row in discovered['rows']:
        check_row(row);center=row['center'];assert center in (3,4)
        a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        key=row['a'],row['b'],center
        if key not in cache:
            try:
                proof=prove(a,b,center,BAD)
                theta=max(bulk,E.cast(proof['core_upper']))
                proof['method']='compatible_past_replacement'
            except AssertionError:
                proof=spec.root(a,b,center)
                theta=E.cast(proof['theta'])
                proof['method']='rational_backward_window'
            proof['theta_upper']=theta.data();cache[key]=proof
        theta=E(tuple(cache[key]['theta_upper']))
        assert theta<=E.cast(row['theta'])
        l,h=(center+E(tuple(v)) for v in row['interval'])
        low,high=max(l,theta),min(h,E.cast(upper))
        assert low<high
        rows.append(dict(row,theta_upper=theta.data(),covered_interval=[low.data(),high.data()]))
    intervals=[tuple(E(tuple(v)) for v in r['covered_interval']) for r in rows]
    components=union(intervals)
    assert components[0][0]==bulk and components[0][1]>Q('4.52')
    selected=[]
    for left,right in components:
        current=left
        while current<right:
            high,index=max((h,i) for i,(l,h) in enumerate(intervals) if l<=current<h)
            selected.append(rows[index]);current=high
    def inside(x,lower):
        denominator=10**8;n=int(float(x)*denominator)
        while E.cast(Q(n,denominator))>x:n-=1
        while E.cast(Q(n+1,denominator))<=x:n+=1
        if lower and E.cast(Q(n,denominator))<x:n+=1
        return Q(n,denominator)
    rational_components=[(inside(l,True),inside(h,False)) for l,h in components]
    for (l,h),(a,b) in zip(components,rational_components):assert l<=a<b<=h
    target=Q('4.51104888'),Q('4.52')
    assert components[0][0]<=target[0]<target[1]<=components[0][1]
    # The bulk endpoint is a periodic Lagrange/Markov value.
    def periodic(w):
        a,b,c,d=matrix(w);disc=(d-a)**2+4*b*c;f=isqrt(disc//41667)
        assert disc==41667*f*f
        x=E.quad(Q(a-d,2*c),Q(f,2*c),41667)
        assert 0<x<1 and cf(w,x)==x
        return x
    word=(3,1,3,1,2,1,3,1,3,2)
    assert scan(word*3) is not None
    periodic_values=[]
    for i,d in enumerate(word):
        left=tuple(word[(i-j)%len(word)] for j in range(1,len(word)+1))
        right=tuple(word[(i+j)%len(word)] for j in range(1,len(word)+1))
        periodic_values.append(d+periodic(left)+periodic(right))
    assert max(periodic_values)==bulk
    # Negative controls: reject an incorrect scale bin and an incompatible past.
    damaged=dict(selected[0],bin=selected[0]['bin']+1)
    try:check_row(damaged)
    except AssertionError:pass
    else:raise AssertionError('Wrong root scale bin accepted')
    try:prove(tuple(map(int,selected[0]['a'])),tuple(map(int,selected[0]['b'])),selected[0]['center'],BAD,damage=True)
    except AssertionError:pass
    else:raise AssertionError('Incompatible past accepted')
    output=DATA/'lower_interval_certificate.json'
    certificate=dict(language=table.meta['language'],basis=E.basis,rows=selected,
                     components=[[v.data() for v in iv] for iv in components],
                     witnesses=[dict(key=list(k),proof=v) for k,v in cache.items()],
                     periodic_endpoint=dict(word='3131213132',local_values=[v.data() for v in periodic_values]))
    output.write_text(json.dumps(certificate,indent=2)+'\n')
    files=[Path(__file__).resolve(),ROOT/'Berstein/src/compatible_past.py',
           ROOT/'Berstein/src/search_313_intervals.py',ROOT/'Berstein/src/prepare_313.py',
           ROOT/'Berstein/src/spectral_rational.py',ROOT/'Berstein/src/field.py',
           DATA/(NAME+'.dat'),DATA/(NAME+'.meta.json'),DATA/(NAME+'.json.alive.bin'),
           DATA/(NAME+'_replay.json'),audit_path,output,source,
           ROOT/'Berstein/audit/independent_kernel.cpp',ROOT/'Berstein/src/graph_kernel.cpp',
           ROOT/'Berstein/logs'/f'{NAME}_independent.log']
    report=dict(passed=True,interval_in_berstein_region_proved=True,
                claim='[4.51104888,4.52] subset L and M',
                exact_first_lower=bulk.data(),exact_first_lower_decimal=float(bulk),
                periodic_bulk_endpoint_in_L_and_M=True,
                lagrange_inclusion_basis='Periodic endpoint plus gluing with 2 separators; all other points exceed the bulk bound.',
                adopted_rows=replay['surviving_states'],independent_failed_cells=0,
                input_side_transitions=audit['transitions'],certificate_rows=len(selected),
                components=certificate['components'],
                components_decimal=[[float(v) for v in iv] for iv in components],
                rational_components=[[str(v) for v in iv] for iv in rational_components],
                negative_controls=2,whole_berstein_conjecture_proved=False,
                lean_formalized=False,
                sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files})
    (DATA/'lower_interval_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256','components')},indent=2))


if __name__=='__main__':main()
