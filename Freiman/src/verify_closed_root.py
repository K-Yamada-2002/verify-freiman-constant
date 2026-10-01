"""Algebraic replay of a root menu extracted from the closed integer table.

Recomputes the parent cover using exact algebraic expressions, checks exact
child parameter images and every destination bit, and verifies that the
listed primitive bands cover each joined interval used by the menu.
"""
import argparse,json
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
from anchor_boxes import AnchorUniform,anchor,derivative_fraction
from exact_cf import parameters,matrix,interval,CF
from obstruction_probe import scan
from box_certificates import suffix_range,child_box,contains

BASE=DATA;A=(3,2,1,1,3);B=(4,3,2,2)


def verify(name,certificate):
    meta=json.loads((BASE/(name+'.meta.json')).read_text())
    proof=json.loads((BASE/(certificate+'.json')).read_text())
    assert proof['closed_family_found'] and proof.get('verification_only')
    bits=(BASE/(name+'.json.alive.bin')).read_bytes();memory=meta['memory'];base=Q(meta['base'])
    keys=[(q,p,tuple(s)) for q,p,s in meta['side_keys']];ids={k:i for i,k in enumerate(keys)}
    S=len(keys);T=len(meta['types']);bins=meta['high']-meta['low']+1
    assert len(bits)==S*S*bins*T and sum(bits)==proof['surviving_states']
    def signature(a):return len(scan(a)),len(a)%2,a[-memory:]
    def bounds(a):
        n=max(memory,len(scan(a)))
        if meta.get('prehistory_interval',['0','1'])==['0','1']:return suffix_range(a,n)
        aa,bb,cc,dd=matrix(tuple(reversed(a[-n:])))
        return tuple(sorted((aa*x+bb)/(cc*x+dd) for x in map(Q,meta['prehistory_interval'])))
    root=meta['root_geometry_id'];rootbin=root%bins+meta['low']
    assert root//bins==ids[signature(A)]*S+ids[signature(B)]
    box=(bounds(A),bounds(B),(base**rootbin,base**(rootbin+1)))
    r,s,rho=parameters(A,B);z=(1+r*anchor(A))/(1+s*anchor(B));scale=rho*z*z
    assert contains(box,((r,r),(s,s),(scale,scale)))
    cert=proof['root_certificate'];parent=cert['parent_type'];assert bits[root*T+parent]
    uniform=AnchorUniform(A,B,meta['types'][parent],box);menu=[];destinations=0
    decoded=[]
    for row in cert['chain']:
        u,w=(tuple(meta['extensions'][i]) for i in row['extension_indices'])
        assert len(u)+len(w)>0 and scan(A+u) is not None and scan(B+w) is not None
        geom=ids[signature(A+u)]*S+ids[signature(B+w)];assert geom==row['destination_geometry']
        rr,ss,_=child_box(box,u,w);assert contains((bounds(A+u),bounds(B+w)),(rr,ss))
        fa=derivative_fraction(A,u,box[0]);fb=derivative_fraction(B,w,box[1])
        image=(box[2][0]*fb[0]/fa[1],box[2][1]*fb[1]/fa[0]);lo,hi=row['scale_bins']
        assert base**lo<=image[0]<=image[1]<=base**(hi+1)
        selected=[]
        for t in row['band_types']:
            selected.append(tuple(map(Q,meta['bands'][t])))
            for i in range(lo,hi+1):
                assert bits[((geom*bins+i-meta['low'])*T+t)]==1;destinations+=1
        joined=[]
        for l,h in sorted(selected):
            if joined and l<=joined[-1][1]:joined[-1]=(joined[-1][0],max(joined[-1][1],h))
            else:joined.append((l,h))
        l,h=(Q(x,meta['scale']) for x in row['joined_band'])
        assert any(x<=l and h<=y for x,y in joined)
        kind='F' if (l,h)==(0,1) else f'band_{l}_{1-h}'
        menu.append((u,w,kind));decoded.append({'u':u,'w':w,'band':[str(l),str(h)],'scale_bins':[lo,hi],
                                             'primitive_types':row['band_types']})
    assert uniform.verify(menu)
    # The entire surviving portion of this root is a genuine interval union.
    root_bands=[tuple(map(Q,meta['bands'][t])) for t in range(T) if bits[root*T+t]]
    joined=[]
    for l,h in sorted(root_bands):
        if joined and l<=joined[-1][1]:joined[-1]=(joined[-1][0],max(joined[-1][1],h))
        else:joined.append((l,h))
    L,U=interval(A,B);assert 4+L==CF
    spectral_intervals=[(4+L+l*(U-L),4+L+h*(U-L)) for l,h in joined]
    result={'passed':True,'closed_states_replayed':proof['surviving_states'],
            'exact_root_menu':decoded,'checked_destination_memberships':destinations,
            'root_scale_bin':rootbin,'root_box':[[str(x) for x in pair] for pair in box],
            'root_parent_band':meta['bands'][parent],
            'root_surviving_bands':[[str(l),str(h)] for l,h in joined],
            'markov_intervals':[[x.data(),y.data()] for x,y in spectral_intervals],
            'markov_intervals_decimal':[[float(x),float(y)] for x,y in spectral_intervals],
            'includes_freiman_endpoint':any(l==0 for l,h in joined),
            'freiman_ray_proved':False}
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('name');p.add_argument('--certificate');a=p.parse_args()
    result=verify(a.name,a.certificate or a.name+'_replay')
    (BASE/(a.name+'_algebraic_replay.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
