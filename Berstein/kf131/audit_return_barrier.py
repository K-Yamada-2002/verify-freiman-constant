#!/usr/bin/env python3
"""Audit an obstruction to closing the CURRENT finite scalar atlas.

This is not a claim about interior, new types, longer moves, or a verifier
allowing shape-domain subdivisions. Every destination allowed by the current
verifier must individually contain the full arriving shape box.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

from exact import state_of
from anchored_geometry import B, shape_image, transition
from verify_type_graph import shape_box, require
from verify_scalar_graph import ScalarVerifier


def audit(data, length=4):
    require(data['roots'] == [0], 'this diagnostic requires root 0 only')
    require(type(length) is int and 1 <= length <= 6, 'invalid bounded word length')
    nodes = data['nodes']
    states = sorted({s for n in nodes for s in n['states']})
    words = [''.join(w) for k in range(length+1) for w in itertools.product('123',repeat=k)]
    boxes = {s:shape_box(s) for s in states}
    matches = {}
    for s in states:
        for w in words:
            try:
                arrival_state = state_of(s+w)
            except ValueError:
                continue
            a,b = shape_image(w,boxes[s])
            matches[s,w] = {t for t in states if state_of(t) == arrival_state
                            and boxes[t][0] <= a <= b <= boxes[t][1]}
    leading = lambda s:len(s)-len(s.lstrip('2'))
    potential = [sum(map(leading,n['states'])) for n in nodes]
    edges = []
    for i,n in enumerate(nodes):
        for u in words:
            for v in words:
                if not 0 < len(u)+len(v) <= length:
                    continue
                left = matches.get((n['states'][0],u),set())
                right = matches.get((n['states'][1],v),set())
                if not left or not right:
                    continue
                for j,m in enumerate(nodes):
                    if m['parity'] != n['parity']*(-1)**(len(u)+len(v)):
                        continue
                    a,b = m['states']
                    if (a in left and b in right) or (b in left and a in right):
                        edges.append(dict(source=i,target=j,suffixes=[u,v]))
    # Any nonroot type in a closed finite component would need a successor
    # of smaller potential, and cannot reach root if root has maximal potential.
    strict = all(potential[e['target']] < potential[e['source']]
                 for e in edges if e['source'] != 0)
    maximal_root = potential[0] == max(potential)
    result = dict(max_total_length=length,shape_edges=edges,potentials=potential,
                  nonroot_potential_strictly_decreases=strict,root_potential_maximal=maximal_root,
                  scope='existing types and current uniform-core verifier only',
                  closure_impossible_in_this_atlas=False)
    if not strict or not maximal_root:
        result['status'] = 'this potential does not establish a barrier'
        return result
    checker = ScalarVerifier(data)
    root_actions = sorted({tuple(e['suffixes']) for e in edges if e['source'] == e['target'] == 0})
    cores,accepted,rejected = [],[],[]
    for u,v in root_actions:
        _,_,h,_ = transition(u,v,*checker.box(0),nodes[0]['parity'])
        cases = []
        if h[0] <= 1:
            cases.append(dict(swap=False,interval=list(nodes[0]['interval']),destinations=[0]))
        if h[1] > 1:
            cases.append(dict(swap=True,interval=list(nodes[0]['interval']),destinations=[0]))
        edge = dict(suffixes=[u,v],cases=cases)
        try:
            core,_ = checker.scalar_child(0,edge)
        except ValueError as error:
            rejected.append(dict(suffixes=[u,v],reason=str(error)))
            continue
        cores.append(core)
        accepted.append(dict(edge=edge,core=[B.coerce(x).record() for x in core]))
    current,end = checker.interval(nodes[0]['interval'])
    while current < end:
        choices = [b for a,b in cores if a <= current < b]
        if not choices:
            break
        current = max(choices)
    result.update(root_only_actions=accepted,rejected_root_actions=rejected,
                  root_covered_by_root_only_actions=current >= end,
                  closure_impossible_in_this_atlas=current < end,
                  status='all nonroot types eliminate; root-only full-interval offers do not cover root'
                         if current < end else 'root-only cover may close; run the full verifier')
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--length',type=int,default=4)
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    raw = args.source.read_bytes()
    result = audit(json.loads(raw),args.length)
    result.update(source=str(args.source),source_sha256=hashlib.sha256(raw).hexdigest())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('shape_edges','potentials','root_only_actions','rejected_root_actions')}))


if __name__ == '__main__':
    main()
