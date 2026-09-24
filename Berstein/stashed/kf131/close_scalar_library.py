#!/usr/bin/env python3
"""Seek a greatest fixed point using only existing scalar types.

Recompute parameter x scalar offers after each deletion. Keeping one greedy
rule per parent, or requiring every redundant rectangle forever, can miss
valid returns. Successful rules still pass the independent ScalarVerifier.
"""
import argparse
from bisect import bisect_left,bisect_right
import copy
import hashlib
import itertools
import json
from pathlib import Path

from exact import state_of
from anchored_geometry import B,shape_image,transition
from verify_type_graph import shape_box
from verify_scalar_graph import verifier_for


def merge(intervals):
    out = []
    for a,b in sorted(intervals):
        if a >= b:
            continue
        if out and a <= out[-1][1]:
            out[-1] = out[-1][0],max(out[-1][1],b)
        else:
            out.append((a,b))
    return out


def common_fragments(hbox,rectangles):
    """Intervals whose ENTIRE product with hbox is covered by rectangles."""
    lo,hi = map(B.coerce,hbox)
    cuts = {lo,hi}
    for hb,_ in rectangles:
        cuts.update(B.coerce(x) for x in hb if lo < x < hi)
    cuts = sorted(cuts)
    parts = None
    for a,b in list(zip(cuts,cuts[1:])) or [(lo,hi)]:
        spans = merge([span for hb,span in rectangles if hb[0] <= a <= b <= hb[1]])
        parts = spans if parts is None else merge([(max(c,e),min(d,f))
                       for c,d in parts for e,f in spans])
        if not parts:
            return []
    return parts or []


class RatioIndex:
    """Exact intersection queries, including nested boxes and endpoints."""
    def __init__(self,boxes):
        self.lower=sorted((a,j) for j,(a,b) in boxes)
        self.upper=sorted((b,j) for j,(a,b) in boxes)
        self.sentinel=max((j for j,_ in boxes),default=-1)+1

    def intersecting(self,required):
        a,b=required
        left=bisect_right(self.lower,(b,self.sentinel))
        right=bisect_left(self.upper,(a,-1))
        return sorted({j for _,j in self.lower[:left]} & {j for _,j in self.upper[right:]})


def geometry_moves(data,length,return_blocks=False):
    verifier = verifier_for(data)
    nodes = data['nodes']
    states = {s for n in nodes for s in n['states']}
    boxes = {s:shape_box(s) for s in states}
    by_states = {}
    for j,n in enumerate(nodes):
        by_states.setdefault((n['parity'],*n['states']),[]).append(j)
    words = [''.join(w) for k in range(length+1) for w in itertools.product('123',repeat=k)]
    pairs = {(u,v) for u in words for v in words if 0 < len(u)+len(v) <= length}
    if return_blocks:
        # End each side with a saved shape word, so a long move can jump
        # directly back into that shape box. This is a targeted family,
        # not enumeration of all words up to the resulting longer length.
        for n in nodes:
            for a,b in (n['states'],n['states'][::-1]):
                pairs.update((p+a,q+b) for p in ('','1','2','3') for q in ('','1','2','3'))
    pairs = sorted(pairs)
    words = sorted({w for pair in pairs for w in pair})
    matches = {}
    for s in states:
        for w in words:
            try:
                end = state_of(s+w)
            except ValueError:
                continue
            a,b = shape_image(w,boxes[s])
            matches[s,w] = {t for t in states if state_of(t) == end and boxes[t][0] <= a <= b <= boxes[t][1]}
    result = [[] for n in nodes]
    ratio_indices={}
    for i,n in enumerate(nodes):
        verifier.check_initial_hull(i)
        for u,v in pairs:
            left,right = matches.get((n['states'][0],u),set()),matches.get((n['states'][1],v),set())
            if not left or not right:
                continue
            parity = n['parity']*(-1)**(len(u)+len(v))
            possible = {
                False:sorted(j for a in left for b in right
                             for j in by_states.get((parity,a,b),[])),
                True:sorted(j for a in left for b in right
                            for j in by_states.get((parity,b,a),[]))}
            if not any(possible.values()):
                continue
            _,_,h,_ = transition(u,v,*verifier.box(i),n['parity'])
            requests = []
            if h[0] <= 1:
                requests.append((False,(h[0],min(h[1],B(1)))))
            if h[1] > 1:
                requests.append((True,(1/h[1],min(1/h[0],B(1)))))
            cases = []
            for swap,required in requests:
                key=tuple(possible[swap])
                if key not in ratio_indices:
                    ratio_indices[key]=RatioIndex([(j,verifier.box(j)[2]) for j in key])
                dests=ratio_indices[key].intersecting(required)
                try:
                    verifier.covers_ratio(required,[verifier.box(j)[2] for j in dests])
                except ValueError:
                    break
                cases.append((swap,required,dests))
            else:
                result[i].append((u,v,cases))
    return result


def close(data,length=4,return_blocks=False):
    verifier = verifier_for(data)
    moves = geometry_moves(data,length,return_blocks)
    active = set(range(len(data['nodes'])))
    rounds = []
    selected = {}
    while active:
        selected = {}
        for i in sorted(active):
            parent = data['nodes'][i]
            candidates = []
            for u,v,cases in moves[i]:
                options = []
                for swap,hbox,dests in cases:
                    dests = [j for j in dests if j in active]
                    rectangles = [(verifier.box(j)[2],tuple(data['nodes'][j]['interval'])) for j in dests]
                    spans = common_fragments(hbox,rectangles)
                    offers = []
                    for span in spans:
                        used = [j for j in dests if max(span[0],data['nodes'][j]['interval'][0])
                                < min(span[1],data['nodes'][j]['interval'][1])]
                        case = dict(swap=swap,interval=list(span),destinations=used)
                        core = verifier.transport(i,u,v,swap,verifier.interval(span),used)
                        offers.append((case,core))
                    options.append(offers)
                for combination in itertools.product(*options):
                    a,b = max(c[1][0] for c in combination),min(c[1][1] for c in combination)
                    if a < b:
                        candidates.append(((a,b),dict(suffixes=[u,v],cases=[c[0] for c in combination])))
            current,end = verifier.interval(parent['interval'])
            chosen = []
            while current < end:
                options = [x for x in candidates if x[0][0] <= current < x[0][1]]
                if not options:
                    break
                core,edge = max(options,key=lambda x:x[0][1])
                chosen.append(edge);current = core[1]
            if current >= end:
                selected[i] = chosen
        removed = sorted(active-set(selected))
        rounds.append(dict(active=len(active),removed=removed))
        if not removed:
            break
        active.difference_update(removed)
    result = copy.deepcopy(data)
    for i,n in enumerate(result['nodes']):
        n.update(covered=i in active,children=selected.get(i,[]) if i in active else [])
    checker = verifier_for(result)
    verified = [checker.local(i) for i in sorted(active)]
    report = dict(length=length,return_blocks=return_blocks,
                  longest_retained_move=max((len(u)+len(v) for group in moves for u,v,_ in group),default=0),
                  geometry_successors=[sorted({j for _,_,cases in group for _,_,dests in cases for j in dests})
                                       for group in moves],
                  geometry_moves=sum(map(len,moves)),rounds=rounds,
                  supported_nodes=sorted(active),verified_local_rules=verified,
                  scope='fixed finite library; no claim excluding larger libraries',closed=False)
    if all(j in active for j in data['roots']):
        report['closed_verification'] = checker.closed()
        report['closed'] = True
    result.update(closed_candidate=report['closed'],open_nodes=len(result['nodes'])-len(active),
                  status='finite library return search; physical closure only if explicitly verified')
    return result,report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--length',type=int,default=4,choices=range(1,7))
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--return-blocks',action='store_true')
    args = ap.parse_args()
    raw = args.source.read_bytes()
    data,report = close(json.loads(raw),args.length,args.return_blocks)
    report.update(source=str(args.source),source_sha256=hashlib.sha256(raw).hexdigest())
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    args.output.with_suffix('.closure.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(moves=report['geometry_moves'],supported=len(report['supported_nodes']),closed=report['closed'])))


if __name__ == '__main__':
    main()
