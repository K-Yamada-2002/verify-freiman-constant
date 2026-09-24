#!/usr/bin/env python3
"""Reuse locally proved covers on equal parameter boxes, retaining all children."""
import argparse
import copy
import json
from pathlib import Path

from verify_scalar_graph import ScalarVerifier


def geometry(node):
    return (tuple(node['states']),node['parity'],node['ratio_bin'],
            tuple(node.get('ratio_refinement',[0,0])))


def graft(base, patch, include_roots=False):
    if base['settings'] != patch['settings']:
        raise ValueError('incompatible settings')
    result = copy.deepcopy(base)
    nodes = result['nodes']
    keys = {(geometry(n),tuple(n['interval'])):n['id'] for n in nodes}
    remap = {}
    for node in patch['nodes']:
        key = geometry(node),tuple(node['interval'])
        if key not in keys:
            item = copy.deepcopy(node)
            item.update(id=len(nodes),covered=False,children=[])
            keys[key] = item['id']
            nodes.append(item)
        remap[node['id']] = keys[key]
    if include_roots:
        result['roots'] = list(dict.fromkeys(result['roots']+[remap[j] for j in patch['roots']]))
    offers = {}
    verifier = ScalarVerifier(patch)
    for i,node in enumerate(patch['nodes']):
        if not node['covered']:
            continue
        verifier.local(i)
        for edge in node['children']:
            edge = copy.deepcopy(edge)
            for case in edge['cases']:
                case['destinations'] = [remap[j] for j in case['destinations']]
            offers.setdefault(geometry(node),[]).append(edge)
    checker = ScalarVerifier(result)
    new = []
    for j,node in enumerate(nodes):
        if node['covered'] or geometry(node) not in offers:
            continue
        candidates = []
        for edge in offers[geometry(node)]:
            core,deps = checker.scalar_child(j,edge)
            candidates.append((core,edge))
        current,end = checker.interval(node['interval'])
        chain = []
        while current < end:
            choices = [x for x in candidates if x[0][0] <= current < x[0][1]]
            if not choices:
                break
            core,edge = max(choices,key=lambda x:x[0][1])
            chain.append(edge)
            current = core[1]
        if current >= end:
            node.update(covered=True,children=chain)
            checker.local(j)
            new.append(j)
    # Retain only obligations reachable from the original roots.
    keep,todo = set(),list(result['roots'])
    while todo:
        j = todo.pop()
        if j in keep:
            continue
        keep.add(j)
        if nodes[j]['covered']:
            todo.extend(checker.local(j)['dependencies'])
    order = sorted(keep)
    ids = {old:new for new,old in enumerate(order)}
    kept = []
    for old in order:
        row = copy.deepcopy(nodes[old])
        row['id'] = ids[old]
        for edge in row['children']:
            for case in edge['cases']:
                case['destinations'] = [ids[j] for j in case['destinations']]
        kept.append(row)
    result.update(nodes=kept,roots=[ids[j] for j in result['roots']],
                  open_nodes=sum(not n['covered'] for n in kept),closed_candidate=False)
    final = ScalarVerifier(result)
    for j in range(len(kept)):
        final.check_initial_hull(j)
        if kept[j]['covered']:
            final.local(j)
    report = dict(nodes=len(kept),open_nodes=result['open_nodes'],
                  verified_local_rules=len(final.checked),newly_covered_reachable=sum(j in keep for j in new),
                  roots=len(result['roots']),status='exact local patch; open obligations remain')
    return result,report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('base',type=Path)
    ap.add_argument('patch',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--include-roots',action='store_true')
    args = ap.parse_args()
    data,report = graft(json.loads(args.base.read_text()),json.loads(args.patch.read_text()),args.include_roots)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)


if __name__ == '__main__':
    main()
