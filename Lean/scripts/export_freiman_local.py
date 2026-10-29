#!/usr/bin/env python3
"""Propose finite local menus, raw exact labels, derivative boxes and destinations.

All output is untrusted and must pass the Lean semantic and covering checkers.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import isqrt
import json
import sys
import hashlib

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent
sys.path.insert(0, str(REPO / "Freiman"))
import proof as P
import prepare as F

NAMES = ["entry", "period", "three_a", "three_b"]
DEN = 2**240
SQDEN = 10**240
SQ = isqrt(462*SQDEN*SQDEN)
SQBOX = Q(SQ,SQDEN),Q(SQ+1,SQDEN)


def as_k(v):
    if isinstance(v,F.K):
        return v
    v=F.E.cast(v)
    assert v.coeff[1:3] == (0,0)
    return F.K(v.coeff[0],v.coeff[3])


def enclose(v):
    v=as_k(v)
    lo=v.a+min(v.b*z for z in SQBOX)
    hi=v.a+max(v.b*z for z in SQBOX)
    a=(lo*DEN).numerator//(lo*DEN).denominator
    b=-((-hi*DEN).numerator//(-hi*DEN).denominator)
    return Q(a,DEN),Q(b,DEN)


def mul(a,b):
    values=[x*y for x in a for y in b]
    return min(values),max(values)


def add(a,b): return a[0]+b[0],a[1]+b[1]

def div(a,b):
    assert b[0]>0
    return mul(a,(1/b[1],1/b[0]))


def convert_box(a,b,box,to):
    r,s,v=box
    x,y=enclose(F.anchor(a)),enclose(F.anchor(b))
    z=P.zeta_enclosure()
    one=(Q(1),Q(1))
    lx,lz=[add(one,mul(r,t)) for t in (x,z)]
    ry,rz=[add(one,mul(s,t)) for t in (y,z)]
    f=mul(div(lz,lx),div(ry,rz)) if to else mul(div(lx,lz),div(rz,ry))
    return mul(v,mul(f,f))


def export():
    source=REPO/'Freiman/certificates/ray.json'
    ray=json.loads(source.read_text())
    rows={r['name']:r for r in ray['local_conditions']}
    kernel=P.Kernel(source.parent)
    boxes={n:P.read_box(rows[n]) for n in NAMES}
    protos={'entry':(P.A,P.B),'period':(P.A+P.U,P.B+P.V),
            'three_a':(P.LEFT,P.RIGHT),'three_b':(P.LEFT,P.RIGHT)}
    def spec(word,shape):
        return [len(F.scan(word)),bool(len(word)%2),shape]
    specs={n:[spec(w,sh) for w,sh in zip(protos[n],boxes[n][:2])] for n in NAMES}
    def general_spec(i):
        q,p,_=kernel.meta['side_keys'][i]
        proto=tuple(kernel.meta['prototypes'][i])
        length=max(kernel.memory,q)
        aa,bb,cc,dd=F.matrix(tuple(reversed(proto[-length:])))
        shp=tuple(sorted((aa*t+bb)/(cc*t+dd) for t in map(Q,kernel.meta.get('prehistory_interval',['0','1']))))
        return [q,bool(p),shp]
    def key_spec(s):return s[0],s[1],tuple(s[2])
    def build_side(proto,source_spec,children):
        raw=[];ids={}
        def raw_id(v):
            v=as_k(v)
            if v not in ids:ids[v]=len(raw);raw.append(v)
            return ids[v]
        raw_id(F.anchor(proto))
        raw_id(F.side_pairs(F.scan(proto),len(proto)%2,(),'base')[1])
        transitions=[];extensions=[];targets=[];stepids={}
        for ext,dest in [((),source_spec)]+children:
            key=tuple(ext),key_spec(dest)
            if key in stepids:continue
            stepids[key]=len(extensions)
            extensions.append(tuple(ext));targets.append(dest)
            low,high=F.side_pairs(F.scan(proto),len(proto)%2,tuple(ext),'base')
            li,hi=raw_id(low),raw_id(high)
            dl,dh=F.derivative_fraction(proto,tuple(ext),source_spec[2])
            derivative=enclose(dl)[0],enclose(dh)[1]
            transitions.append([0,False,0,derivative,li,hi])
        return {'spec':source_spec,'raw':raw,'transitions':transitions,
                'extensions':extensions,'targets':targets,'stepids':stepids}
    conditions=[]
    for name in NAMES:
        row=rows[name];a,b=protos[name]
        box=boxes[name]
        if name.startswith('three'):
            outer=convert_box(a,b,box,False)
        else:outer=box[2]
        # Widen rational corners slightly so Lean's independent radical bounds fit.
        if name.startswith('three'):
            outer=(outer[0]-Q(1,10**30),outer[1]+Q(1,10**30))
        parent_box=box[:2]+(outer,)
        menu,_=P.certify_menu(kernel,a,b,parent_box,tuple(map(Q,row['band'])),
            [dict(v,destination='kernel' if v['destination']=='general' else v['destination']) for v in row['menu']],lambda v:None)
        children=[[],[]]
        for v in menu:
            if v['destination']=='kernel':
                ia,ib=divmod(v['geometry'],kernel.sides)
                dest=[general_spec(ia),general_spec(ib)]
            else:dest=specs[v['destination']]
            v['specs']=dest
            for i,key in enumerate(('u','w')):children[i].append((tuple(v[key]),dest[i]))
        sides=[build_side(proto,sp,ch) for proto,sp,ch in zip((a,b),specs[name],children)]
        for v in menu:
            v['steps']=[sides[i]['stepids'][(tuple(v[key]),key_spec(v['specs'][i]))] for i,key in enumerate(('u','w'))]
        # The source list has pairwise intersections; retain a path between boundary anchors.
        target=tuple(map(Q,row['band']))
        probe=P.AnchorUniform(a,b,f'band_{target[0]}_{1-target[1]}',parent_box)
        words=[(tuple(v['u']),tuple(v['w']),f'band_{Q(v["band"][0])}_{1-Q(v["band"][1])}') for v in menu]
        left=next(i for i,v in enumerate(words) if probe.left_anchor(v))
        right=next(i for i in range(len(words)-1,-1,-1) if probe.right_anchor(words[i]))
        selected=menu[left:right+1] if left<=right else list(reversed(menu[right:left+1]))
        conditions.append({'name':name,'sides':sides,'band':target,'invariant':box[2],
                           'scale':outer,'menu':selected})
    tokens=[str(len(conditions))]
    def natural(n):tokens.append(str(int(n)))
    def rat(q):
        q=Q(q);tokens.extend((str(q.numerator),str(q.denominator)))
    def bounds(b):rat(b[0]);rat(b[1])
    def quad(q):q=as_k(q);rat(q.a);rat(q.b)
    def spec_tokens(s):natural(s[0]);natural(s[1]);bounds(s[2])
    def word(w):natural(len(w));tokens.extend(map(str,w))
    for kind,c in enumerate(conditions):
        natural(kind)
        for side in c['sides']:
            spec_tokens(side['spec'])
            natural(len(side['raw']))
            for v in side['raw']:quad(v);bounds(enclose(v))
            natural(len(side['transitions']))
            for tr,w,dst in zip(side['transitions'],side['extensions'],side['targets']):
                bounds(tr[3]);natural(tr[4]);natural(tr[5]);word(w);spec_tokens(dst)
        bounds(c['band']);bounds(c['invariant']);bounds(c['scale'])
        natural(len(c['menu']))
        for v in c['menu']:
            natural(v['steps'][0]);natural(v['steps'][1]);bounds(v['band'])
            if v['destination']=='kernel':
                natural(0)
                ia,ib=divmod(v['geometry'],kernel.sides)
                for n in (ia,ib,v['bins'][0]-kernel.low,v['bins'][1]-kernel.low,sum(1<<t for t in v['types'])):natural(n)
            else:
                natural(NAMES.index(v['destination'])+1)
    path=HERE/'generated/freiman_local.txt'
    path.parent.mkdir(exist_ok=True);path.write_text(' '.join(tokens)+'\n')
    manifest={'conditions':len(conditions),'local_vertices':[len(c['menu']) for c in conditions],
              'raw_counts':[[len(s['raw']) for s in c['sides']] for c in conditions],
              'local_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
              'ray_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    (path.parent/'freiman_local_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest


if __name__=='__main__':print(json.dumps(export(),indent=2))
