#!/usr/bin/env python3
"""Explore coarser destination domains while preserving the physical root.

All newly added scalar intervals are unproved placeholders. Width audits
depend only on the parameter domains, not on those placeholder intervals.
"""
import argparse
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path

from audit_return_widths import audit
from graft_gap_repairs import geometry
from verify_scalar_graph import ScalarVerifier
from exact import F
from anchored_geometry import parameters
from add_gap_repair_moves import add_moves


def enlarge(source, memory=2, refinement=0, radius=0, replace_original=False, coarse_base=None):
    if memory < 2 or not 0 <= refinement <= 16 or radius < 0:
        raise ValueError('invalid domain enlargement')
    result = copy.deepcopy(source)
    original = ScalarVerifier(source)
    if coarse_base is not None:
        if not replace_original or refinement != 0:
            raise ValueError('base change requires replacement and refinement zero')
        base = F(coarse_base)
        if not 0 < base < 1:
            raise ValueError('invalid base')
        result['settings']['base'] = str(base)
        floor = original.base**source['settings']['bins']
        bins = 1
        while base**bins > floor:
            bins += 1
        result['settings']['bins'] = bins
    if replace_original:
        result['nodes'] = [copy.deepcopy(source['nodes'][j]) for j in source['roots']]
        result['roots'] = list(range(len(result['nodes'])))
        for i,n in enumerate(result['nodes']):
            n['id'] = i
            if coarse_base is not None:
                h = parameters(*source['root_prefixes'])[2]
                q = next(q for q in range(bins) if base**(q+1) <= h <= base**q)
                n.update(ratio_bin=q,ratio_refinement=[0,0])
    # Retain all original domains, but never transplant conditional rules.
    for n in result['nodes']:
        n.update(covered=False, children=[])
    keys = {geometry(n) for n in result['nodes']}
    for old_i,n in enumerate(source['nodes']):
        level, part = n.get('ratio_refinement', [0, 0])
        if refinement > level:
            raise ValueError('requested refinement is not a coarsening')
        central = [n['ratio_bin']]
        if coarse_base is not None:
            lo,hi = original.box(old_i)[2]
            central = [q for q in range(bins) if base**(q+1) < hi and lo < base**q]
        candidates = {q+offset for q in central for offset in range(-radius,radius+1)}
        for q in sorted(candidates):
            if not 0 <= q < result['settings']['bins']:
                continue
            row = dict(id=len(result['nodes']), states=[s[-memory:] for s in n['states']],
                       parity=n['parity'], ratio_bin=q,
                       ratio_refinement=[refinement, part//2**(level-refinement)],
                       interval=[-1, 1], covered=False, children=[])
            if geometry(row) not in keys:
                keys.add(geometry(row))
                result['nodes'].append(row)
    checker = ScalarVerifier(result)
    for i in range(len(result['nodes'])):
        checker.check_initial_hull(i)
    assert checker.seed() == ScalarVerifier(source).seed()
    result['domain_exploration'] = dict(memory=memory, refinement=refinement, radius=radius,
                                      replace_original=replace_original,
                                      coarse_base=coarse_base,
                                      same_physical_seed=True, closed=False)
    result.update(open_nodes=len(result['nodes']),closed_candidate=False,
                  status='unproved parameter domain exploration')
    return result


def add_successor_domains(source, memory=2, length=1):
    """Add complete arrival ratio covers for the generated legal moves."""
    incoming=dict(settings=copy.deepcopy(source['settings']),
                  nodes={str(n['id']):copy.deepcopy(n) for n in source['nodes']},rules=[])
    with contextlib.redirect_stdout(io.StringIO()):
        add_moves(incoming,list(range(len(source['nodes']))),length=length,
                  memory=memory,refinement=0)
    result=copy.deepcopy(source)
    for n in result['nodes']:
        n.update(covered=False,children=[])
    keys={geometry(n) for n in result['nodes']}
    for n in incoming['nodes'].values():
        if geometry(n) not in keys:
            keys.add(geometry(n))
            n.update(id=len(result['nodes']),interval=[-1,1],covered=False,children=[])
            result['nodes'].append(n)
    checker=ScalarVerifier(result)
    for i in range(len(result['nodes'])):
        checker.check_initial_hull(i)
    assert checker.seed()==ScalarVerifier(source).seed()
    result['successor_expansion']=dict(length=length,memory=memory,refinement=0,
                                      old_nodes=len(source['nodes']),same_seed=True)
    result.update(open_nodes=len(result['nodes']),closed_candidate=False,
                  status='unproved successor domain exploration')
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--memories', type=int, nargs='+', default=[2, 3, 4])
    ap.add_argument('--refinements', type=int, nargs='+', default=[0, 2])
    ap.add_argument('--radius', type=int, default=0)
    ap.add_argument('--length', type=int, default=4)
    ap.add_argument('--replace-original', action='store_true')
    ap.add_argument('--coarse-base')
    ap.add_argument('--successor-depth',type=int,default=0)
    args = ap.parse_args()
    source = json.loads(args.source.read_text())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    results = []
    for memory in args.memories:
        for refinement in args.refinements:
            name = f'memory{memory}_ref{refinement}_radius{args.radius}'
            data = enlarge(source, memory, refinement, args.radius, args.replace_original,args.coarse_base)
            if args.successor_depth:
                name += f'_steps{args.successor_depth}'
                for _ in range(args.successor_depth):
                    data=add_successor_domains(data,memory)
            path = args.output_dir/(name+'.json')
            path.write_text(json.dumps(data, indent=2)+'\n')
            report = audit(data, length=args.length, return_blocks=True)
            report.update(source=str(path), source_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            path.with_suffix('.width.json').write_text(json.dumps(report, indent=2)+'\n')
            summary = dict(name=name, types=report['types'], moves=report['geometry_moves'],
                           status=report['status'])
            results.append(summary)
            print(json.dumps(summary), flush=True)
            (args.output_dir/'summary.json').write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    main()
