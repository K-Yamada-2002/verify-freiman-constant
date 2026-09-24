#!/usr/bin/env python3
"""Certify holes in proposed uniform scalar types, not in physical K_F+K_F.

Discovery uses floats to choose a complete legal subdivision tree. Replay
recomputes every leaf in Q(sqrt(2),sqrt(10)), checks box membership, and checks
that every legal branch is present. Exhaustion never means exclusion.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

from exact import F, extreme_tail, matrix, state_of, step, transform
from anchored_geometry import ALPHA, B, difference_range, parameters as prefix_parameters
from verify_scalar_graph import ScalarVerifier


def require(value, message):
    if not value:
        raise ValueError(message)


@lru_cache(maxsize=32768)
def tail_hull(state, word):
    end = state_of(state+word)
    return tuple(sorted(transform(word,extreme_tail(end,high)[0]) for high in (False,True)))


def legal_children(states, u, v, side):
    prefix = (u,v)[side]
    end = state_of(states[side]+prefix)
    return [(u+d,v) if side == 0 else (u,v+d)
            for d in '123' if step(end,d) is not None]


def normalize(x, r):
    return (x-ALPHA)*(1+r*ALPHA)/(1+r*x)


def exact_hull(states, u, v, parameters, parity):
    r,s,h = parameters
    left = [normalize(B(x),r) for x in tail_hull(states[0],u)]
    right = sorted(parity*h*normalize(B(x),s) for x in tail_hull(states[1],v))
    return left[0]+right[0],left[1]+right[1]


def discover(states, parity, parameters, target, budget=5000, depth=28):
    alpha = 2**0.5-1
    r,s,h = map(float,parameters)
    target = float(target)
    @lru_cache(None)
    def side_hull(side, word):
        shape = (r,s)[side]
        values = [(float(x.a)+float(x.b)*10**0.5-alpha)*(1+shape*alpha)/
                  (1+shape*(float(x.a)+float(x.b)*10**0.5))
                  for x in tail_hull(states[side],word)]
        return tuple(sorted((parity*h*x if side else x) for x in values))
    tree = [dict(u='',v='',children=[])]
    todo = [0]
    while todo:
        i = todo.pop()
        row = tree[i]
        u,v = row['u'],row['v']
        a,b = side_hull(0,u),side_hull(1,v)
        if a[1]+b[1] < target-1e-12 or a[0]+b[0] > target+1e-12:
            continue
        if len(tree)+3 > budget or max(len(u),len(v)) >= depth:
            return None
        side = 0 if a[1]-a[0] >= b[1]-b[0] else 1
        row['side'] = side
        for x,y in legal_children(states,u,v,side):
            j = len(tree)
            row['children'].append(j)
            tree.append(dict(u=x,v=y,children=[]))
            todo.append(j)
    return tree


def replay(certificate):
    node = certificate['type']
    data = dict(schema='kf131-scalar-atlas-v1',settings=certificate['settings'],nodes=[node])
    checker = ScalarVerifier(data)
    parameters = tuple(map(F,certificate['parameters']))
    for value,box in zip(parameters,checker.box(0)):
        require(box[0] <= value <= box[1], 'witness outside parameter box')
    target = F(certificate['target'])
    a,b = checker.interval(node['interval'])
    require(a <= target <= b, 'witness outside assigned interval')
    states = tuple(map(state_of,node['states']))
    tree = certificate['tree']
    require(bool(tree) and (tree[0]['u'],tree[0]['v']) == ('',''), 'wrong tree root')
    todo,seen,margins = [0],set(),[]
    while todo:
        i = todo.pop()
        require(type(i) is int and 0 <= i < len(tree) and i not in seen,'invalid tree index')
        seen.add(i)
        row = tree[i]
        u,v = row['u'],row['v']
        if row['children']:
            require(type(row.get('side')) is int and row['side'] in (0,1),'invalid split side')
            for j in row['children']:
                require(type(j) is int and 0 <= j < len(tree),'invalid child index')
            actual = sorted((tree[j]['u'],tree[j]['v']) for j in row['children'])
            require(actual == sorted(legal_children(states,u,v,row['side'])), 'incomplete legal split')
            todo.extend(row['children'])
        else:
            lo,hi = exact_hull(states,u,v,parameters,node['parity'])
            require(hi < target or target < lo, 'leaf does not exclude witness')
            margins.append(target-hi if hi < target else lo-target)
    require(len(seen) == len(tree),'unreachable tree node')
    return dict(nodes=len(tree),leaves=len(margins),distance_lower_bound=min(margins).record(),
                conclusion='uniform scalar type is false at this parameter; no physical sum exclusion asserted')


def rational_in(box):
    midpoint = (box[0]+box[1])/2
    # Small denominators keep independent exact replay inexpensive.
    value = F(str(B.coerce(midpoint).decimal(20))).limit_denominator(10**8)
    return value if box[0] <= value <= box[1] else midpoint


def uniform_gap(certificate):
    """Reuse a certified tree to try excluding a band on the ENTIRE box.

    Failure is inconclusive. Returning a band proves it is avoided at every
    parameter of this box, including parameters of any physical prefix pair.
    """
    replay(certificate)
    node = certificate['type']
    checker = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',
                                  settings=certificate['settings'],nodes=[node]))
    states = tuple(map(state_of,node['states']))
    p = node['parity']
    below,above = [],[]
    t = F(certificate['target'])
    for row in certificate['tree']:
        if row['children']:
            continue
        left = tail_hull(states[0],row['u'])
        right = tail_hull(states[1],row['v'])
        low = (left[0],right[0] if p > 0 else right[1])
        high = (left[1],right[1] if p > 0 else right[0])
        lo = difference_range(low,(ALPHA,ALPHA),*checker.box(0),p)[0]
        hi = difference_range(high,(ALPHA,ALPHA),*checker.box(0),p)[1]
        if hi < t:
            below.append(hi)
        elif t < lo:
            above.append(lo)
        else:
            return None
    if not below or not above:
        return None
    a,b = max(below),min(above)
    require(a < t < b,'invalid uniform gap')
    return [a.record(),b.record()]


def physical_obstruction(certificate):
    """Check an actual cylinder pair realizes the bad type and avoids a band."""
    replay(certificate)  # also validates completeness of the tree
    node = certificate['type']
    u,v = certificate['physical_prefixes']
    states = tuple(map(state_of,node['states']))
    require(tuple(map(state_of,(u,v))) == states,'wrong physical states')
    r,s,h,p = prefix_parameters(u,v)
    require(p == node['parity'],'wrong physical parity')
    checker = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',
                                  settings=certificate['settings'],nodes=[node]))
    for value,box in zip((r,s,h),checker.box(0)):
        require(box[0] <= value <= box[1],'physical parameters escape type')
    a,b = map(F,certificate['physical_scalar_gap'])
    lo,hi = checker.interval(node['interval'])
    require(lo <= a < b <= hi,'invalid physical gap')
    for row in certificate['tree']:
        if row['children']:
            continue
        x,y = exact_hull(states,row['u'],row['v'],(r,s,h),p)
        require(y < a or b < x,'physical gap is not excluded')
    _,_,c,d = matrix(u)
    center = transform(u,ALPHA)+transform(v,ALPHA)
    scale = (-1)**len(u)/(c*ALPHA+d)**2
    values = sorted(center+scale*t for t in (a,b))
    return dict(prefixes=[u,v],gap=[x.record() for x in values],
                conclusion='this closed interval avoids this cylinder-pair sum only')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('diagnostics',type=Path,nargs='?')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--replay',type=Path)
    ap.add_argument('--limit',type=int,default=16)
    ap.add_argument('--budget',type=int,default=2000)
    args = ap.parse_args()
    if args.replay:
        data = json.loads(args.replay.read_text())
        for row in data['obstructions']:
            result = dict(node=row['source_node'],uniform_gap=uniform_gap(row),**replay(row))
            if 'physical_prefixes' in row:
                result['physical'] = physical_obstruction(row)
            print(json.dumps(result),flush=True)
        return
    require(args.diagnostics is not None and args.output is not None,'input and output required')
    diagnostic = json.loads(args.diagnostics.read_text())
    candidates = {r['node']:r for r in diagnostic['one_missing']+diagnostic['most_shared_unexpanded']}
    settings = diagnostic['settings']
    result = dict(source_sha256=diagnostic['source_sha256'],obstructions=[],unresolved=[])
    for index,row in enumerate(list(candidates.values())[:args.limit]):
        node = row['type']
        checker = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',settings=settings,nodes=[node]))
        params = tuple(rational_in(box) for box in checker.box(0))
        a,b = checker.interval(node['interval'])
        found = None
        for t in (a,b,(a+b)/2,(3*a+b)/4,(a+3*b)/4):
            tree = discover(tuple(map(state_of,node['states'])),node['parity'],params,t,args.budget)
            if tree is None:
                continue
            cert = dict(source_node=row['node'],type=node,settings=settings,
                        parameters=list(map(str,params)),target=str(t),tree=tree)
            cert['verification'] = replay(cert)
            cert['uniform_gap'] = uniform_gap(cert)
            result['obstructions'].append(cert)
            found = cert
            break
        if found is None:
            result['unresolved'].append(row['node'])
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(dict(checked=index+1,node=row['node'],excluded=found is not None,
                              tree_nodes=len(found['tree']) if found else None)),flush=True)


if __name__ == '__main__':
    main()
