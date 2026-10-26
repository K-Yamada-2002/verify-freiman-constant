"""Universal local Lem2 rows and a conservative finite-table closure check.

All box bounds and all comparisons are exact. A local row by itself is NOT a
proof that its children remain admissible. Closure is checked separately.
"""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
from layout import DATA
from exact_cf import K, cf, matrix, parameters, tail_endpoint
from obstruction_probe import scan, step


def signature(a,b):
    return (len(scan(a)),len(scan(b)),len(a)%2,len(b)%2)


def side_values(state,parity,word):
    for d in word:
        state=step(state,d)
        if state is None:raise ValueError('Forbidden child')
    values=sorted(cf(word,tail_endpoint(state,m)) for m in (True,False))
    return tuple(values if not parity else reversed(values))


def endpoint_pairs(a,b,u=(),w=()):
    left=side_values(scan(a),len(a)%2,u)
    right=side_values(scan(b),len(b)%2,w)
    return (left[0],right[0]),(left[1],right[1])


def delta_range(x,y,box,sign):
    # phi_r(x)-phi_r(y) has this cancellation-free form and is monotone in r.
    vals=[sign*(x-y)/((1+t*x)*(1+t*y)) for t in box]
    return min(vals),max(vals)


def difference_lower(x,y,box,pa,pb):
    da=delta_range(x[0],y[0],box[0],(-1)**pa)
    db=delta_range(x[1],y[1],box[1],(-1)**pb)
    terms=[rho*v for rho in box[2] for v in db]
    return da[0]+min(terms)


def local_certificate(a,b,menu,box):
    parent=endpoint_pairs(a,b)
    endpoints=[endpoint_pairs(a,b,u,w) for u,w in menu]
    if not any(x[0]==parent[0] for x in endpoints):return False
    if not any(x[1]==parent[1] for x in endpoints):return False
    # A chain is sufficient; certify BOTH inequalities on every edge.
    for first,second in zip(endpoints,endpoints[1:]):
        if difference_lower(first[1],second[0],box,len(a)%2,len(b)%2)<0:return False
        if difference_lower(second[1],first[0],box,len(a)%2,len(b)%2)<0:return False
    return True


def suffix_range(word,n):
    suffix=tuple(reversed(word[-n:]))
    a,b,c,d=matrix(suffix)
    vals=[Q(a*t+b,c*t+d) for t in (0,1)]
    return min(vals),max(vals)


def child_box(box,u,w):
    def one(bounds,word):
        a,b,c,d=matrix(word)
        vals=[(c+r*a)/(d+r*b) for r in bounds]
        growth=[d+r*b for r in bounds]
        return (min(vals),max(vals)),(min(growth),max(growth))
    rr,qa=one(box[0],u);ss,qb=one(box[1],w)
    rho=(box[2][0]*(qa[0]/qb[1])**2,box[2][1]*(qa[1]/qb[0])**2)
    return (rr,ss,rho)


def make_row(a,b,menu):
    rho=parameters(a,b)[2]
    for suffix in (2,3,4,5,6,8,12):
        for power in range(2,14):
            factor=Q(1,2**power)
            box=(suffix_range(a,suffix),suffix_range(b,suffix),
                 (rho*(1-factor),rho*(1+factor)))
            if local_certificate(a,b,menu,box):
                return {'a':a,'b':b,'signature':signature(a,b),'box':box,'menu':menu,
                        'children':[{'signature':signature(a+u,b+w),
                                     'box':child_box(box,u,w)} for u,w in menu]}
    return None


def intersection(a,b):
    c=tuple((max(x[0],y[0]),min(x[1],y[1])) for x,y in zip(a,b))
    return c if all(lo<=hi for lo,hi in c) else None


def contains(outer,inner):
    return all(lo<=ll and hh<=hi for (lo,hi),(ll,hh) in zip(outer,inner))


def subtract(box,cut):
    common=intersection(box,cut)
    if common is None:return [box]
    if contains(cut,box):return []
    # Retain boundary faces redundantly: this is a conservative closed cover
    # of box\cut and avoids relying on open/closed arithmetic for strict faces.
    out=[];middle=list(box)
    for axis,((lo,hi),(cl,ch)) in enumerate(zip(box,common)):
        if lo<cl:
            part=middle.copy();part[axis]=(lo,cl);out.append(tuple(part))
        if ch<hi:
            part=middle.copy();part[axis]=(ch,hi);out.append(tuple(part))
        middle[axis]=(cl,ch)
    return out


def covered(box,regions,cap=1000):
    if any(contains(r,box) for r in regions):return True
    remaining=[box]
    for region in regions:
        remaining=[piece for old in remaining for piece in subtract(old,region)]
        if not remaining:return True
        if len(remaining)>cap:return False # Unknown is never accepted.
    return False


def closure(rows):
    active=set(range(len(rows)));rounds=[]
    while active:
        regions={}
        for i in active:regions.setdefault(rows[i]['signature'],[]).append(rows[i]['box'])
        remove={i for i in active if any(not covered(c['box'],regions.get(c['signature'],[]))
                                       for c in rows[i]['children'])}
        rounds.append({'before':len(active),'removed':len(remove)})
        if not remove:break
        active-=remove
    return sorted(active),rounds


def encode_box(box):return [[str(a),str(b)] for a,b in box]


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--input',default='menus_I7_L6_G3.json')
    p.add_argument('--output',default='universal_local_rows.json')
    args=p.parse_args();base=DATA
    data=json.loads((base/args.input).read_text());rows=[];unresolved=[]
    for record in data['records']:
        if record['status']!='exact_local_cover':continue
        a,b=tuple(map(int,record['a'])),tuple(map(int,record['b']))
        menu=[(tuple(u),tuple(w)) for u,w in record['menu']]
        row=make_row(a,b,menu)
        if row:row['source_id']=record['id'];rows.append(row)
        else:unresolved.append(record['id'])
    active,rounds=closure(rows)
    a,b=map(tuple,data['root']);pt=tuple((p,p) for p in parameters(a,b))
    root_in_closed_table=covered(pt,[rows[i]['box'] for i in active if rows[i]['signature']==signature(a,b)])
    output=[]
    for row in rows:
        out={**row,'a':list(row['a']),'b':list(row['b']),'box':encode_box(row['box']),
             'children':[{**c,'box':encode_box(c['box'])} for c in row['children']]}
        output.append(out)
    result={'proof_complete':root_in_closed_table,'scope':'31313-restricted sum for the specified root only.',
            'root':data['root'],'rows':output,'unresolved_local_rows':unresolved,
            'closure_rounds':rounds,'closed_row_ids':active,'root_in_closed_table':root_in_closed_table}
    (base/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
    print('universal local rows',len(rows),flush=True)
