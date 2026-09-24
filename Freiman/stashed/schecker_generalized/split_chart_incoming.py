#!/usr/bin/env python3
"""Split refuted open types by incoming images instead of their convex hull.

Each saved incoming destination gets a separate restricted obligation. Every
edge and initial family is rechecked, and all unresolved clones stay open.
This may increase the number of obligations; it is a geometric repair, not
a proof of closure or of filledness of the new types.
"""
import argparse
import copy
import json
from pathlib import Path

from chart_geometry import Domain, relative_box
from contract_cyclic_domains import domains, intersection
from contract_piecewise_charts import prune, restrict, rules, select_destinations
from reduce_chart_frontier import counts
from type_graph_geometry import decode
from verify_piecewise_charts import PiecewiseVerifier


def split_incoming(data, targets, allow_local=False):
    data = copy.deepcopy(data)
    checker = PiecewiseVerifier(data)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('invalid source rules')
    targets = set(targets)
    if not targets <= set(range(len(data['nodes']))):
        raise ValueError('only unresolved nodes may be split: invalid target')
    if not allow_local and not targets <= set(audit['open_nodes']):
        raise ValueError('only unresolved nodes may be split')
    if targets & set(data['roots'].values()):
        raise ValueError('initial families must retain their full domains')
    original_count = len(data['nodes'])
    for i, node in enumerate(data['nodes']):
        node.setdefault('incoming_lineage', i)
    clones, changed, redundant = {}, 0, 0
    for node in data['nodes'][:original_count]:
        for rule in rules(node):
            part = checker.cells[rule['cell']]
            for edge in rule['children']:
                child = part.extend(*edge['suffixes'], edge['high'])
                if any(d['node'] in targets for d in edge['destinations']):
                    selected = select_destinations(checker, child, edge)
                    redundant += len(edge['destinations'])-len(selected)
                    edge['destinations'] = selected
                for dest in edge['destinations']:
                    index = dest['node']
                    if index not in targets:
                        continue
                    old = data['nodes'][index]
                    target = checker.cells[old['cell']]
                    image = relative_box(child.exchange() if dest['swap'] else child, target)
                    # Non-covering auxiliary charts can occur in an edge.
                    # Leave these intact rather than infer their irrelevance.
                    if image is None:
                        continue
                    bounds = intersection(domains(image), domains(target.base))
                    if bounds is None or bounds == domains(target.base):
                        continue
                    narrowed = restrict(target, bounds)
                    key = index, narrowed
                    if key not in clones:
                        cid = len(checker.cells)
                        checker.cells.append(narrowed)
                        data['cells'].append(narrowed.record())
                        clone = copy.deepcopy(old)
                        clone['cell'] = cid
                        clone['incoming_split_origin'] = index
                        if clone.get('pieces'):
                            pieces = []
                            for piece in clone['pieces']:
                                guard = checker.cells[piece['cell']]
                                clipped = intersection(domains(guard.base), bounds)
                                if clipped is None:
                                    continue
                                restricted = restrict(guard, clipped)
                                piece['cell'] = len(checker.cells)
                                checker.cells.append(restricted)
                                data['cells'].append(restricted.record())
                                pieces.append(piece)
                            if not pieces:
                                raise ValueError('restriction lost every guard')
                            clone['pieces'] = pieces
                        clones[key] = len(data['nodes'])
                        data['nodes'].append(clone)
                    dest['node'] = clones[key]
                    changed += 1
    # The parent's whole successor image must still be covered after routing.
    fresh = PiecewiseVerifier(data)
    after = fresh.audit()
    if after['failed_rules']:
        raise ValueError('split failed independent local replay')
    data = prune(data)
    replay = PiecewiseVerifier(data).audit()
    if replay['failed_rules']:
        raise ValueError('pruning failed independent replay')
    return data, dict(targets=sorted(targets), clones_created=len(clones),
                      redirected_references=changed, redundant_references=redundant,
                      counts=counts(data)), replay


def witness_membership(source, result, witnesses):
    """Track old counterexample points, not absence of any other gaps."""
    before = [Domain.read(c) for c in source['cells']]
    after = [Domain.read(c) for c in result['cells']]
    rows = []
    from audit_chart_gaps import point_checker
    checker = PiecewiseVerifier(source)
    for row in witnesses:
        old = source['nodes'][row['node']]
        domain = before[old['cell']]
        point = tuple(map(decode, row['base_parameters']))
        actual = point_checker(checker, row['node'], point).cells[0]
        point_domain = Domain(actual, ('', ''), actual.high)
        candidates, retained = [], []
        for i, node in enumerate(result['nodes']):
            target = after[node['cell']]
            same = (node['lower'] == old['lower'] and node['upper'] == old['upper']
                    and target == domain)
            orientations=[d['swap'] for d in node.get('incoming_origins',[]) if d['node']==row['node']]
            if node.get('incoming_lineage',node.get('incoming_split_origin'))==row['node'] or same:
                orientations.append(False)
            if not orientations:
                continue
            candidates.append(i)
            for swap in set(orientations):
                image = relative_box(point_domain.exchange() if swap else point_domain, target)
                if image is not None and all(a <= lo == hi <= b for (lo,hi),(a,b)
                                             in zip(domains(image),domains(target.base))):
                    retained.append(i);break
        rows.append(dict(source_node=row['node'], replacement_nodes=candidates,
                         witness_retained_in=retained))
    return dict(status='membership of old counterexample points after splitting; not filledness',
                source_proof_hash=PiecewiseVerifier(source).proof_hash(),
                split_proof_hash=PiecewiseVerifier(result).proof_hash(), rows=rows)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--gaps', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--propagate-parents', action='store_true',
                    help='first split excluded ancestors from exact backward traces')
    args = ap.parse_args()
    data = json.loads(args.graph.read_text())
    gaps = json.loads(args.gaps.read_text())
    checker = PiecewiseVerifier(data)
    if gaps['source_proof_hash'] != checker.proof_hash():
        raise ValueError('gap report has a different source graph')
    from audit_chart_gaps import backward_trace, replay
    for row in gaps['witnesses']:
        replay(checker, row)
    source = data
    parent_summary = None
    if args.propagate_parents:
        targets = {r['node'] for r in gaps['witnesses']}
        ancestors = set()
        def collect(trace):
            if trace['status'] == 'excluded' and trace['node'] not in targets:
                ancestors.add(trace['node'])
            for parent in trace.get('parents', []):
                collect(parent)
        for row in gaps['witnesses']:
            trace = backward_trace(checker, row, gaps.get('backward_depth') or 6)
            if trace['status'] != 'excluded':
                raise ValueError('ancestor repair requires an excluded witness')
            collect(trace)
        if ancestors:
            data, parent_summary, _ = split_incoming(data, ancestors, allow_local=True)
        leaf_targets = [i for i,n in enumerate(data['nodes'])
                        if n.get('incoming_lineage', i) in targets]
    else:
        leaf_targets = [r['node'] for r in gaps['witnesses']]
    result, summary, audit = split_incoming(data, leaf_targets)
    summary['parent_split'] = parent_summary
    result['incoming_split'] = dict(source_proof_hash=checker.proof_hash(), **summary)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    membership = witness_membership(source, result, gaps['witnesses'])
    args.output.with_suffix('.witnesses.json').write_text(json.dumps(membership, indent=2)+'\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
