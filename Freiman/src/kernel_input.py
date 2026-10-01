"""Prepare a finite universe for greatest-fixed-point numerical discovery.

No local-row counting is a success criterion. Surviving states must cover
themselves using successors in the same finite universe. C++ results remain
conjectural until exact coverage and transition replay succeeds.
"""
import argparse,json
from itertools import product
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
from obstruction_probe import scan,STATES,extremal_tail
from box_certificates import suffix_range,child_box
from typed_boxes import side_pairs
from typed_intervals import endpoints
from width_catalog import normalized_difference_range,width,phi
from exact_cf import parameters,matrix

BASE=DATA

def prepare(memory,length,base,low,high,name,bands=False,grid=0,anchor=False,macro=False,spine=0):
    def key(a):return len(scan(a)),len(a)%2,a[-memory:]
    prototypes={}
    for n in range(memory,max(memory,4)+2):
        for a in product((1,2,3),repeat=n):
            if scan(a) is not None:prototypes.setdefault(key(a),a)
    keys=sorted(prototypes);ids={k:i for i,k in enumerate(keys)}
    extensions=[u for n in range(length+1) for u in product((1,2,3),repeat=n)]
    pairs=[(i,j) for i,u in enumerate(extensions) for j,w in enumerate(extensions)
           if 0<len(u)+len(w)<=length]
    if macro:
        period=(1,3,1,2,1,3)
        rotations=[period[i:]+period[:i] for i in range(6)]
        for word in rotations:
            if word not in extensions:extensions.append(word)
        pairs.extend((extensions.index(u),extensions.index(w)) for u in rotations for w in rotations)
    def lower_spine(a):
        pre,period=extremal_tail(scan(a),len(a)%2==0)
        return (pre+period*(spine+1))[:spine]
    if spine:
        for a in prototypes.values():
            tail=lower_spine(a)
            for n in range(spine):
                for d in (1,2,3):
                    word=tail[:n]+(d,)
                    if word not in extensions:extensions.append(word)
    unrestricted=set(pairs)
    pairs=[(i,j,0) for i,j in sorted(unrestricted)]
    if spine:
        pairs.extend((i,j,1) for i,u in enumerate(extensions) for j,w in enumerate(extensions)
                     if 0<len(u)==len(w)<=spine and (i,j) not in unrestricted)
    a,b=(3,2,1,1,3),(4,3,2,2);r,s,rho=parameters(a,b)
    if anchor:
        xa=side_pairs(scan(a),len(a)%2,(),'base')[0]
        xb=side_pairs(scan(b),len(b)%2,(),'base')[0]
        z=(1+r*xa)/(1+s*xb);R=float(rho*z*z)
    else:R=float(rho*width(scan(b),s)/width(scan(a),r))
    import math
    rootbin=math.floor(math.log(R)/math.log(float(base)))
    root=(ids[key(a)]*len(keys)+ids[key(b)])*(high-low+1)+(rootbin-low)
    types=[('F',0,0,0),('T2',1,0,0),('L2',2,0,0),('R2',3,0,0),('B2',4,0,0)]
    if bands:
        for trim in (Q(1,10),Q(1,4),Q(2,5)):
            for left,right in ((trim,0),(0,trim),(trim,trim)):
                types.append((f'band_{left}_{right}',5,left,right))
    if grid:
        for i in range(grid-1):
            left,right=Q(i,grid),1-Q(i+2,grid)
            if not any(t[1:]==(5,left,right) for t in types):
                types.append((f'band_{left}_{right}',5,left,right))
    lines=[f'{len(keys)} {len(extensions)} {low} {high} {float(base):.17g} {length} {root} {len(types)} {len(pairs)}']
    lines.append(' '.join(str(len(u)) for u in extensions))
    lines.extend(f'{kind} {float(left):.17g} {float(right):.17g}' for _,kind,left,right in types)
    lines.extend(f'{i} {j} {restricted}' for i,j,restricted in pairs)
    for k in keys:
        a=prototypes[k];state=scan(a);bounds=suffix_range(a,max(memory,k[0]))
        for u in extensions:
            if scan(a+u) is None:lines.append('-1');continue
            child=ids[key(a+u)]
            xlo,xhi=side_pairs(state,0,u,'base')
            if anchor:
                xanchor=side_pairs(state,len(a)%2,(),'base')[0]
                childanchor=side_pairs(scan(a+u),len(a+u)%2,(),'base')[0]
                A,B,C,D=matrix(u)
                zs=[(1+r*xanchor)/((C+r*A)*childanchor+D+r*B) for r in bounds]
                fa=sorted(z*z for z in zs)
            else:fa=normalized_difference_range(state,xhi,xlo,bounds)
            values=[]
            for lang in ('base','binary'):
                xx=side_pairs(state,len(a)%2,u,lang)
                for r in bounds:
                    if anchor:values.extend(float((-1)**len(a)*(x-xanchor)*(1+r*xanchor)/(1+r*x)) for x in xx)
                    else:values.extend(float((-1)**len(a)*phi(r,x)/width(state,r)) for x in xx)
            on_spine=bool(u) and len(u)<=spine and u[:-1]==lower_spine(a)[:len(u)-1]
            lines.append(' '.join([str(child),str(int(on_spine)),f'{float(fa[0]):.17g}',f'{float(fa[1]):.17g}']+
                                  [f'{v:.17g}' for v in values]))
    (BASE/(name+'.dat')).write_text('\n'.join(lines)+'\n')
    metadata={'memory':memory,'length':length,'base':str(base),'low':low,'high':high,
              'types':[t[0] for t in types],'type_data':[[name,kind,str(left),str(right)] for name,kind,left,right in types],
              'side_keys':keys,'prototypes':[prototypes[k] for k in keys],
              'extensions':extensions,'root_geometry_id':root,'root_width_ratio':R,
              'coordinate':'lower_endpoint_derivative_ratio' if anchor else 'persistent_width_ratio',
              'successor_pairs':pairs,
              'spine_depth':spine,
              'scope':'Numerical finite-kernel discovery; not a proof.'}
    (BASE/(name+'.meta.json')).write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps({'sides':len(keys),'geometry_cells':len(keys)**2*(high-low+1),
                      'typed_cells':len(keys)**2*(high-low+1)*len(types),'root':root}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--memory',type=int,default=2)
    p.add_argument('--length',type=int,default=3);p.add_argument('--base',default='11/10')
    p.add_argument('--low',type=int,default=-24);p.add_argument('--high',type=int,default=24)
    p.add_argument('--name',default='kernel_m2');p.add_argument('--bands',action='store_true')
    p.add_argument('--grid',type=int,default=0);p.add_argument('--anchor',action='store_true')
    p.add_argument('--macro',action='store_true');p.add_argument('--spine',type=int,default=0);a=p.parse_args()
    prepare(a.memory,a.length,Q(a.base),a.low,a.high,a.name,a.bands,a.grid,a.anchor,a.macro,a.spine)
