#!/usr/bin/env python3
"""Combine equivalent conjunctions of open interval obligations.

Same box plus touching scalar intervals can be replaced by their union.
Dyadic sibling boxes with the same scalar interval can be replaced by their
parent box. No assertion is marked filled, and roots are never changed.
"""
import argparse
import copy
import json
from pathlib import Path

from graft_gap_repairs import geometry
from verify_scalar_graph import ScalarVerifier


def coalesce(data):
    result = copy.deepcopy(data)
    nodes = {n['id']:n for n in result['nodes']}
    redirects = {}
    roots = set(result['roots'])
    merges = []
    def combine(a,b,kind):
        redirects[b] = a
        nodes.pop(b)
        merges.append(dict(kept=a,removed=b,kind=kind))
    while True:
        changed = False
        groups = {}
        for j,n in nodes.items():
            if not n['covered'] and j not in roots:
                groups.setdefault(geometry(n),[]).append(j)
        for group in groups.values():
            group.sort(key=lambda j:nodes[j]['interval'])
            if not group:
                continue
            current = group[0]
            for j in group[1:]:
                a,b = nodes[current],nodes[j]
                if b['interval'][0] <= a['interval'][1]:
                    a['interval'][1] = max(a['interval'][1],b['interval'][1])
                    combine(current,j,'scalar union')
                    changed = True
                else:
                    current = j
        groups = {}
        for j,n in nodes.items():
            level,part = n.get('ratio_refinement',[0,0])
            if n['covered'] or j in roots or not level:
                continue
            k = tuple(n['states']),n['parity'],n['ratio_bin'],level,part//2,tuple(n['interval'])
            groups.setdefault(k,[]).append(j)
        for group in groups.values():
            if len(group) != 2:
                continue
            a,b = group
            level,part = nodes[a]['ratio_refinement']
            if part == nodes[b]['ratio_refinement'][1]:
                continue
            nodes[a]['ratio_refinement'] = [level-1,part//2]
            combine(a,b,'dyadic union')
            changed = True
        if not changed:
            break
    order = sorted(nodes)
    ids = {old:new for new,old in enumerate(order)}
    def destination(j):
        while j in redirects:
            j = redirects[j]
        return ids[j]
    kept = []
    for j in order:
        n = nodes[j]
        n['id'] = ids[j]
        for edge in n['children']:
            for case in edge['cases']:
                case['destinations'] = list(dict.fromkeys(destination(k) for k in case['destinations']))
        kept.append(n)
    result.update(nodes=kept,roots=[ids[j] for j in result['roots']],
                  open_nodes=sum(not n['covered'] for n in kept),closed_candidate=False)
    checker = ScalarVerifier(result)
    for j,n in enumerate(kept):
        checker.check_initial_hull(j)
        if n['covered']:
            checker.local(j)
    return result,dict(merges=merges,before=len(data['nodes']),after=len(kept),
                       status='equivalent open obligations; no filling asserted')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    result,report = coalesce(json.loads(args.graph.read_text()))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    args.output.with_suffix('.coalesce.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
