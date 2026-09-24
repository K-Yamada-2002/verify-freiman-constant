#!/usr/bin/env python3
"""Apply smaller conditional parent covers and propagate interval restrictions.

All intervals only decrease. Missing children remain open. The root may become
smaller, so its physical interval is recomputed rather than silently preserved.
An empty surviving component or failure to stabilize is an explicit failure.
"""
import argparse
import copy
import json
from pathlib import Path

from graft_gap_repairs import geometry,graft
from repair_gap_intervals import rounded
from verify_scalar_graph import ScalarVerifier


def attach_partial(base,patch):
    if base['settings'] != patch['settings']:
        raise ValueError('incompatible settings')
    result = copy.deepcopy(base)
    nodes = result['nodes']
    remap = {}
    targets = set()
    for j in patch['roots']:
        n = patch['nodes'][j]
        target = n['source_node']
        if not isinstance(target,int) or not 0 <= target < len(base['nodes']) or target in targets:
            raise ValueError('ambiguous patch source')
        old = nodes[target]
        if geometry(old) != geometry(n) or not old['interval'][0] <= n['interval'][0] < n['interval'][1] <= old['interval'][1]:
            raise ValueError('partial patch does not restrict its source type')
        ScalarVerifier(patch).local(j)
        old.update(interval=list(n['interval']),covered=True,children=[])
        remap[j] = target
        targets.add(target)
    keys = {(geometry(n),tuple(n['interval'])):n['id'] for n in nodes}
    for j,n in enumerate(patch['nodes']):
        if j in remap:
            continue
        key = geometry(n),tuple(n['interval'])
        if key not in keys:
            row = copy.deepcopy(n)
            row.update(id=len(nodes),covered=False,children=[])
            keys[key] = row['id']
            nodes.append(row)
        remap[j] = keys[key]
    for j in patch['roots']:
        edges = copy.deepcopy(patch['nodes'][j]['children'])
        for edge in edges:
            for case in edge['cases']:
                case['destinations'] = list(dict.fromkeys(remap[k] for k in case['destinations']))
        nodes[remap[j]]['children'] = edges
    return result


def contract(data,max_passes=128):
    result = copy.deepcopy(data)
    changes = []
    grid = result['settings']['grid']
    checker = ScalarVerifier(result)
    for iteration in range(max_passes):
        changed = False
        reachable = set()
        pending = list(result['roots'])
        while pending:
            j = pending.pop()
            if j in reachable:
                continue
            reachable.add(j)
            n = result['nodes'][j]
            if n['covered']:
                pending.extend(k for e in n['children'] for c in e['cases'] for k in c['destinations'])
        demands = {}
        for j in reachable:
            n = result['nodes'][j]
            if not n['covered']:
                continue
            for edge in n['children']:
                for case in edge['cases']:
                    destinations = []
                    for k in case['destinations']:
                        a,b = result['nodes'][k]['interval']
                        a,b = max(a,case['interval'][0]),min(b,case['interval'][1])
                        if a < b:
                            demands.setdefault(k,[]).append((a,b))
                            destinations.append(k)
                    if destinations != case['destinations']:
                        case['destinations'] = destinations
                        changed = True
        for j,requests in demands.items():
            if j in result['roots']:
                continue
            n = result['nodes'][j]
            interval = [min(a for a,b in requests),max(b for a,b in requests)]
            if interval != n['interval']:
                changes.append(dict(node=j,before=n['interval'],after=interval,iteration=iteration,reason='incoming scalar demands'))
                n['interval'] = interval
                changed = True
        for node in reversed(result['nodes']):
            if not node['covered'] or node['id'] not in reachable:
                continue
            candidates = []
            for old in node['children']:
                edge = copy.deepcopy(old)
                valid = True
                for case in edge['cases']:
                    intervals = [result['nodes'][j]['interval'] for j in case['destinations']]
                    a = max([case['interval'][0]]+[a for a,b in intervals])
                    b = min([case['interval'][1]]+[b for a,b in intervals])
                    if a >= b:
                        valid = False
                        break
                    case['interval'] = [a,b]
                if not valid:
                    continue
                try:
                    core,_ = checker.scalar_child(node['id'],edge)
                except ValueError:
                    continue
                a,b = checker.interval(node['interval'])
                lo,hi = max(a,core[0]),min(b,core[1])
                if lo < hi:
                    candidates.append(((lo,hi),edge))
            components = []
            for (a,b),_ in sorted(candidates,key=lambda row:row[0][0]):
                if components and a <= components[-1][1]:
                    components[-1][1] = max(b,components[-1][1])
                else:
                    components.append([a,b])
            if not components:
                raise ValueError(f'no surviving conditional core for node {node["id"]}')
            a,b = max(components,key=lambda ab:ab[1]-ab[0])
            interval = [rounded(a,grid,True),rounded(b,grid,False)]
            if interval[0] >= interval[1]:
                raise ValueError(f'surviving interval below grid resolution at node {node["id"]}')
            current,end = checker.interval(interval)
            chosen = []
            while current < end:
                available = [row for row in candidates if row[0][0] <= current < row[0][1]]
                if not available:
                    raise ValueError('internal union coverage failure')
                core,edge = max(available,key=lambda row:row[0][1])
                chosen.append(edge)
                current = core[1]
            if interval != node['interval'] or chosen != node['children']:
                changes.append(dict(node=node['id'],before=node['interval'],after=interval,iteration=iteration))
                node.update(interval=interval,children=chosen)
                changed = True
        if not changed:
            break
    else:
        raise ValueError('interval contraction did not stabilize')
    # Fresh verifier: never reuse results computed before an interval changed.
    result,_ = graft(result,result)
    checker = ScalarVerifier(result)
    for n in result['nodes']:
        checker.check_initial_hull(n['id'])
        if n['covered']:
            checker.local(n['id'])
    report = dict(changes=changes,passes=iteration+1,closed=False,
                  open_nodes=sum(not n['covered'] for n in result['nodes']))
    if 'root_prefixes' in result:
        report['physical_interval'] = checker.seed()
    return result,report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--patch',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    base = json.loads(args.graph.read_text())
    patch = json.loads(args.patch.read_text())
    result,report = contract(attach_partial(base,patch))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    args.output.with_suffix('.contraction.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
