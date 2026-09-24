#!/usr/bin/env python3
"""Partition open scalar obligations without shrinking their union or the seed.

All pieces remain mandatory wherever the old interval was requested. Atlas
product coverage is rechecked; splitting itself proves no new interval.
"""
import argparse
import copy
import json
from pathlib import Path

from verify_scalar_graph import ScalarVerifier
from verify_type_graph import require


def split(data, parts=4, targets=None, cut_points=None):
    require(data['schema'] == 'kf131-scalar-atlas-v1', 'scalar atlas required')
    require(type(parts) is int and parts >= 2, 'at least two pieces required')
    targets = [j for j,n in enumerate(data['nodes']) if not n['covered']] if targets is None else list(targets)
    require(len(set(targets)) == len(targets), 'duplicate target')
    cut_points = {} if cut_points is None else cut_points
    require(set(cut_points).issubset(targets), 'cuts specified for an unselected target')
    before = ScalarVerifier(data)
    for j,n in enumerate(data['nodes']):
        before.check_initial_hull(j)
        if n['covered']:
            before.local(j)
    result = copy.deepcopy(data)
    nodes = result['nodes']
    mapping = {}
    for j in targets:
        require(type(j) is int and 0 <= j < len(data['nodes']), 'invalid target')
        require(not data['nodes'][j]['covered'] and j not in data['roots'],
                'only open non-root obligations may be split')
        source = data['nodes'][j]
        a,b = source['interval']
        if j in cut_points:
            interior = list(cut_points[j])
            require(bool(interior) and all(type(x) is int and a < x < b for x in interior)
                    and sorted(set(interior)) == interior, 'invalid interior cut points')
            cuts = [a]+interior+[b]
        else:
            require(b-a >= parts, 'not enough scalar grid cells')
            cuts = [a+(b-a)*k//parts for k in range(parts+1)]
        ids = []
        for k,(lo,hi) in enumerate(zip(cuts,cuts[1:])):
            new = copy.deepcopy(source)
            index = j if k == 0 else len(nodes)
            new.update(id=index,interval=[lo,hi],covered=False,children=[])
            if k == 0:
                nodes[j] = new
            else:
                nodes.append(new)
            ids.append(index)
        mapping[j] = ids
    for n in nodes:
        for edge in n['children']:
            for case in edge['cases']:
                a,b = case['interval']
                destinations = []
                for j in case['destinations']:
                    destinations.extend(k for k in mapping.get(j,[j])
                                        if max(a,nodes[k]['interval'][0]) < min(b,nodes[k]['interval'][1]))
                case['destinations'] = list(dict.fromkeys(destinations))
    after = ScalarVerifier(result)
    checks = []
    for j,n in enumerate(nodes):
        after.check_initial_hull(j)
        if n['covered']:
            checks.append(after.local(j))
    report = dict(partitions=mapping,local_checks=checks,
                  status='equivalent conjunction of open interval obligations; no filling proved')
    if 'root_prefixes' in data:
        require(before.seed() == after.seed(), 'physical seed changed')
        report['seed'] = after.seed()
    result['open_nodes'] = sum(not n['covered'] for n in nodes)
    result['status'] = report['status']
    result['closed_candidate'] = False
    return result,report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--parts',type=int,default=4)
    ap.add_argument('--nodes',type=int,nargs='+')
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    result,report = split(json.loads(args.source.read_text()),args.parts,args.nodes)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    args.output.with_suffix('.split.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(nodes=len(result['nodes']),open_nodes=result['open_nodes'])))


if __name__ == '__main__':
    main()
