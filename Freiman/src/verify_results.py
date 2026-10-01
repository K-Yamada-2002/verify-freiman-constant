"""Replay arithmetic and local certificates; never promotes them to a ray proof.

The independent sign checker brackets sqrt(462) with rational numbers. Box
inequalities are rechecked at all corners using direct Möbius expressions,
not the range evaluator used to generate the certificate.
"""
import json
from fractions import Fraction as Q
from functools import cmp_to_key
from itertools import product
from math import isqrt
from pathlib import Path
from layout import DATA
import exact_cf as e
import obstruction_probe as p
from box_certificates import endpoint_pairs,signature
from spectral_bounds import bound_root,bulk_maximum
from deep_audit import exact_gap_around

BASE=DATA


def sign(x):
    x=e.K.cast(x)
    if x.a==0 and x.b==0:return 0
    scale=10**12
    while True:
        sq=isqrt(462*scale*scale)
        ends=[x.a+x.b*Q(sq,scale),x.a+x.b*Q(sq+1,scale)]
        lo,hi=min(ends),max(ends)
        if lo>0:return 1
        if hi<0:return -1
        scale*=scale


def independent_union(intervals):
    ordered=sorted(intervals,key=cmp_to_key(lambda x,y:sign(x[0]-y[0])))
    out=[]
    for lo,hi in ordered:
        assert sign(hi-lo)>=0
        if out and sign(out[-1][1]-lo)>=0:
            if sign(hi-out[-1][1])>0:out[-1]=(out[-1][0],hi)
        else:out.append((lo,hi))
    return out


def decode_box(box):return tuple(tuple(map(Q,bounds)) for bounds in box)


def validate_uniform_row(row):
    a,b=tuple(row['a']),tuple(row['b']);box=decode_box(row['box'])
    assert tuple(row['signature'])==signature(a,b)
    assert 0<box[2][0]<=box[2][1]
    menu=[(tuple(u),tuple(w)) for u,w in row['menu']]
    parent=endpoint_pairs(a,b)
    endpoints=[endpoint_pairs(a,b,u,w) for u,w in menu]
    assert any(iv[0]==parent[0] for iv in endpoints)
    assert any(iv[1]==parent[1] for iv in endpoints)
    def value(x,r,s,rho):
        return (-1)**len(a)*x[0]/(1+r*x[0])+rho*(-1)**len(b)*x[1]/(1+s*x[1])
    for first,second in zip(endpoints,endpoints[1:]):
        for r,s,rho in product(*box):
            assert sign(value(first[1],r,s,rho)-value(second[0],r,s,rho))>=0
            assert sign(value(second[1],r,s,rho)-value(first[0],r,s,rho))>=0
    def extend(r,word):
        before,current=r,Q(1)
        for digit in word:before,current=current,digit*current+before
        return before/current,current
    for (u,w),child in zip(menu,row['children']):
        assert len(u)+len(w)>0
        assert tuple(child['signature'])==signature(a+u,b+w)
        vals=[]
        for r,s,rho in product(*box):
            rr,qa=extend(r,u);ss,qb=extend(s,w)
            vals.append((rr,ss,rho*(qa/qb)**2))
        computed=tuple((min(v[i] for v in vals),max(v[i] for v in vals)) for i in range(3))
        assert computed==decode_box(child['box'])


def main():
    counts={}
    # Compare exact endpoints with a separately implemented 160-digit rational
    # enclosure, including prefixes containing 4 and both parities.
    n=0
    for length in range(1,5):
        for word in product((1,2,3,4),repeat=length):
            if p.scan(word) is None:continue
            for mode in (True,False):
                val=e.side_endpoint(word,mode);lo,hi=p.endpoint(word,mode)
                assert sign(val-lo)>=0 and sign(hi-val)>=0
                n+=1
    counts['independent_endpoint_enclosures']=n
    assert e.interval((3,2,1,1,3),(4,3,2,2))[0]+4==e.CF
    # Replay all local-cover records. This validates a finite tree, not its leaves.
    n=0
    for filename in ('menus_I7.json','menus_I7_L6_G3.json'):
        data=json.loads((BASE/filename).read_text());assert not data['proof_complete']
        for row in data['records']:
            if row['status']!='exact_local_cover':continue
            a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
            intervals=[e.interval(a+tuple(u),b+tuple(w)) for u,w in row['menu']]
            assert independent_union(intervals)==[e.interval(a,b)]
            n+=1
    counts['exact_pointwise_local_covers']=n
    data=json.loads((BASE/'universal_local_rows.json').read_text())
    for row in data['rows']:validate_uniform_row(row)
    counts['uniform_local_rows']=len(data['rows'])
    assert not data['closed_row_ids'] and not data['root_in_closed_table']
    root=json.loads((BASE/'spectral_I7.json').read_text())
    replay=bound_root((3,2,1,1,3),(4,3,2,2))
    assert root==json.loads(json.dumps(replay)) and root['theta_le_cF']
    assert bulk_maximum()[0]==e.K(0,Q(4,19))
    counts['all_position_spectral_bound_I7']=True
    initial=json.loads((BASE/'augmented_roots.json').read_text())
    root_intervals=[]
    for row in initial['selected_roots']:
        aa,bb=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        result=bound_root(aa,bb,row['center'])
        assert row==json.loads(json.dumps(result))
        if row['conditional_markov_interval']:
            root_intervals.append(tuple(e.K(*v) for v in row['conditional_markov_interval']))
    components=independent_union(root_intervals)
    assert [[v.data() for v in iv] for iv in components]==initial['exact_conditional_components']
    counts['conditional_root_spectral_bounds']=len(initial['selected_roots'])
    counts['conditional_root_components']=len(components)
    gaps=json.loads((BASE/'root_deep_audit.json').read_text())['records']
    checked=0
    for row in gaps:
        if row['status']!='certified_intrinsic_gap':continue
        a,b=tuple(map(int,row['a'])),tuple(map(int,row['b']))
        lo,hi=[e.K(*v) for v in row['gap']]
        assert exact_gap_around(a,b,row['depth'],(lo+hi)/2)==(lo,hi)
        checked+=1
    counts['replayed_intrinsic_gap_certificates']=checked
    # Corruption controls for the two recurrent failure modes.
    assert len(independent_union([(e.K(0),e.K(1)),(e.K(2),e.K(3))]))==2
    first=json.loads((BASE/'menus_I7.json').read_text())['records'][0]
    aa,bb=tuple(map(int,first['a'])),tuple(map(int,first['b']))
    u,w=first['menu'][0]
    assert independent_union([e.interval(aa+tuple(u),bb+tuple(w))])!=[e.interval(aa,bb)]
    counts['corruption_controls']=2
    counts['freiman_ray_proved']=False
    (BASE/'verification_results.json').write_text(json.dumps(counts,indent=2)+'\n')
    print(json.dumps(counts,indent=2))


if __name__=='__main__':main()
