#!/usr/bin/env python3
"""Find exact counterexamples missed by testing five scalar points.

At an interior parameter, form a finite outer approximation of the whole
assigned interval. Float gaps are only proposals; complete legal exclusion
trees are independently replayed in the exact number field before acceptance.
"""
import argparse
from bisect import bisect_left,bisect_right
from functools import lru_cache
import hashlib
import json
from itertools import product
from pathlib import Path

from exact import F,state_of,step
from scalar_obstructions import rational_in,tail_hull,discover,replay
from verify_scalar_graph import ScalarVerifier


@lru_cache(None)
def tails(state, depth):
    words = ['']
    for _ in range(depth):
        words = [w+d for w in words for d in '123' if step(state_of(state+w),d) is not None]
    def real(x):
        return float(x.a)+float(x.b)*10**0.5
    return [tuple(map(real,tail_hull(state,w))) for w in words]


@lru_cache(maxsize=12)
def adaptive_tails(state,epsilon):
    """Complete legal cylinder cover with approximately equal tail widths.

    Word depth is a poor resolution measure for continued fractions: runs of
    ones shrink much more slowly than runs of threes. Float stopping is only
    for discovery; no positive inclusion conclusion is drawn from this cover.
    """
    if not 0 < epsilon < 1:
        raise ValueError('epsilon must lie between zero and one')
    pending = ['']
    leaves = []
    while pending:
        word = pending.pop()
        a,b = (float(x.a)+float(x.b)*10**0.5 for x in tail_hull(state,word))
        if b-a <= epsilon:
            leaves.append((a,b))
            continue
        if len(word) >= 64 or len(leaves)+len(pending) > 200000:
            raise ValueError('adaptive outer approximation budget exhausted')
        pending.extend(word+d for d in '123' if step(state_of(state+word),d) is not None)
    return leaves


def outer_sum_gaps(left,right,interval):
    """Merge each translated row before the global union.

    For a left interval of width w, adjacent right intervals join exactly
    when their separating gap is at most w. A max tree skips entire groups
    of such gaps without allocating every pairwise sum interval.
    This is only float discovery; exclusion is still independently replayed.
    """
    low,high = map(float,interval)
    starts,ends = [a for a,b in right],[b for a,b in right]
    size = 1
    while size < len(right):
        size *= 2
    tree = [-float('inf')]*(2*size)
    for j in range(len(right)-1):
        tree[size+j] = starts[j+1]-ends[j]
    for j in range(size-1,0,-1):
        tree[j] = max(tree[2*j],tree[2*j+1])
    def barriers(first,last,width):
        pending = [(1,0,size)]
        while pending:
            j,a,b = pending.pop()
            if b <= first or last <= a or tree[j] <= width:
                continue
            if b-a == 1:
                yield a
            else:
                middle = (a+b)//2
                pending.extend(((2*j+1,middle,b),(2*j,a,middle)))
    covered = []
    def compact(rows):
        merged = []
        for a,b in sorted(rows):
            if a > b:
                continue
            if merged and a <= merged[-1][1]:
                merged[-1] = merged[-1][0],max(merged[-1][1],b)
            else:
                merged.append((a,b))
        return merged
    pending_count = 0
    for a,b in left:
        first = bisect_left(ends,low-b-1e-12)
        last = bisect_right(starts,high-a+1e-12)
        if first >= last:
            continue
        start = first
        for end in barriers(first,last-1,b-a):
            covered.append((max(low,a+starts[start]),min(high,b+ends[end])))
            pending_count += 1
            start = end+1
        covered.append((max(low,a+starts[start]),min(high,b+ends[last-1])))
        pending_count += 1
        if pending_count >= 8192:
            covered = compact(covered)
            pending_count = 0
            # A subset already covers the query, so remaining rows cannot
            # produce a gap. This is still only a numerical search result.
            if len(covered) == 1 and covered[0][0] <= low and high <= covered[0][1]:
                return []
    current = low
    gaps = []
    for a,b in sorted(covered):
        if b < current:
            continue
        if current+1e-11 < a:
            gaps.append((current,a))
        current = max(current,b)
    if current+1e-11 < high:
        gaps.append((current,high))
    return sorted(gaps,key=lambda x:x[1]-x[0],reverse=True)


def sampled_gaps(node,parameters,interval,depth,epsilon=None):
    alpha = 2**0.5-1
    states = tuple(map(state_of,node['states']))
    families = []
    r,s,h = map(float,parameters)
    for side,shape in enumerate((r,s)):
        factor = 1 if side == 0 else node['parity']*h
        family = []
        family_tails = tails(states[side],depth) if epsilon is None else adaptive_tails(states[side],epsilon)
        for a,b in family_tails:
            values = [factor*(x-alpha)*(1+shape*alpha)/(1+shape*x) for x in (a,b)]
            family.append(tuple(sorted(values)))
        families.append(sorted(family))
    return outer_sum_gaps(*families,interval)


def witnesses(boxes, corners=False):
    yield tuple(rational_in(box) for box in boxes)
    if corners:
        # Interior points near the eight corners, with exact membership checks.
        for fractions in product((F(1,4),F(3,4)),repeat=3):
            values = []
            for (a,b),q in zip(boxes,fractions):
                x = a+(b-a)*q
                values.append(rational_in((x-(b-a)/16,x+(b-a)/16)))
            yield tuple(values)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--depth',type=int,default=7)
    ap.add_argument('--budget',type=int,default=10000)
    ap.add_argument('--scope',choices=('open','roots','all'),default='open')
    ap.add_argument('--corners',action='store_true')
    ap.add_argument('--epsilon',type=float)
    args = ap.parse_args()
    raw = args.graph.read_bytes()
    data = json.loads(raw)
    v = ScalarVerifier(data)
    result = dict(source_sha256=hashlib.sha256(raw).hexdigest(),depth=args.depth,epsilon=args.epsilon,selection=args.scope,
                  obstructions=[],unresolved=[],parameter_samples=9 if args.corners else 1,
                  scope='whole finite outer approximation at sampled parameters; no positive filling proof')
    checked = 0
    for j,node in enumerate(data['nodes']):
        if args.scope == 'open' and node['covered'] or args.scope == 'roots' and j not in data['roots']:
            continue
        interval = v.interval(node['interval'])
        found = False
        for params in witnesses(v.box(j),args.corners):
            gaps = sampled_gaps(node,params,interval,args.depth,args.epsilon)
            for a,b in gaps[:16]:
                t = F(str((a+b)/2))
                if not interval[0] <= t <= interval[1]:
                    continue
                tree = discover(tuple(map(state_of,node['states'])),node['parity'],params,t,args.budget)
                if tree is None:
                    continue
                cert = dict(source_node=node.get('source_node',j),graph_node=j,type=node,settings=data['settings'],
                            parameters=list(map(str,params)),target=str(t),tree=tree)
                cert['verification'] = replay(cert)
                result['obstructions'].append(cert)
                found = True
                break
            if found:
                break
        else:
            result['unresolved'].append(j)
        checked = len(result['obstructions'])+len(result['unresolved'])
        if checked % 10 == 0:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            print(json.dumps(dict(checked=checked,excluded=len(result['obstructions']))),flush=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(checked=checked,excluded=len(result['obstructions']))),flush=True)


if __name__ == '__main__':
    main()
