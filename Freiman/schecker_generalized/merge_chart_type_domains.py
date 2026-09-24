#!/usr/bin/env python3
"""Merge same-chart, same-interval nodes when exact boxes tile a hull.

This is a conservative quotient: each merged node carries the audited rule
for every original parameter box as a guarded piece. A node with no rule is
absorbed only when its whole box lies inside that proved hull. The ordinary
PiecewiseVerifier and ``closed()`` remain the acceptance checks.
"""
import argparse
import argparse
import copy
import json
from collections import defaultdict
from pathlib import Path

from chart_geometry import Domain
from contract_piecewise_charts import prune
from type_graph_geometry import Cell
from verify_cyclic_types import cover_parameter_box, contains_box
from verify_piecewise_charts import PiecewiseVerifier


def key(node, domain):
    base = domain.base
    return (domain.words, domain.high, base.states, base.parity, base.high,
            tuple(node['lower']), tuple(node['upper']))


def axes(domain):
    return (domain.base.r, domain.base.s, domain.base.ratio)


def locally_defined(node):
    return bool(node.get('children') or node.get('pieces'))


def merge(data):
    data = copy.deepcopy(data)
    checker = PiecewiseVerifier(data)
    before = checker.audit()
    if before['failed_rules']:
        raise ValueError('input contains invalid local rules')

    roots = set(data['roots'].values())
    groups = defaultdict(list)
    for i, node in enumerate(checker.nodes):
        if i in roots:
            continue
        domain = checker.cells[node['cell']]
        groups[key(node, domain)].append(i)

    alias = {}
    merged_rows = []
    for signature, members in groups.items():
        local = [i for i in members if locally_defined(data['nodes'][i])]
        if not local:
            continue
        domains = [checker.cells[data['nodes'][i]['cell']] for i in local]
        boxes = [axes(d) for d in domains]
        hull = tuple((min(box[j][0] for box in boxes),
                      max(box[j][1] for box in boxes)) for j in range(3))
        try:
            cover_parameter_box(hull, boxes)
        except ValueError:
            continue

        representative = min(local)
        rep_node = data['nodes'][representative]
        source_domain = checker.cells[rep_node['cell']]
        base = source_domain.base
        hull_cell = Cell(base.states, base.parity, base.high, *hull).validate()
        hull_domain = Domain(hull_cell, source_domain.words, source_domain.high).validate()
        hull_cid = len(data['cells'])
        data['cells'].append(hull_domain.record())

        pieces = []
        for i in local:
            node = data['nodes'][i]
            if node.get('pieces'):
                pieces.extend(copy.deepcopy(node['pieces']))
            else:
                pieces.append(dict(cell=node['cell'], children=copy.deepcopy(node['children'])))

        # Already proved coverage on the hull lets the merged type subsume any
        # unresolved same-shape obligation whose entire domain lies inside it.
        absorbed = []
        for i in members:
            if i in local or locally_defined(data['nodes'][i]):
                continue
            box = axes(checker.cells[data['nodes'][i]['cell']])
            if all(contains_box(outer, inner) for outer, inner in zip(hull, box)):
                absorbed.append(i)

        rep_node['cell'] = hull_cid
        rep_node['pieces'] = pieces
        rep_node.pop('children', None)
        for i in local + absorbed:
            alias[i] = representative
        merged_rows.append(dict(representative=representative, local_members=local,
                                absorbed_open=absorbed, pieces=len(pieces)))

    if not alias:
        return data, dict(before_nodes=len(data['nodes']), after_nodes=len(data['nodes']),
                          merged_groups=0, merged_local_nodes=0, absorbed_open_nodes=0)

    keep = [i for i in range(len(data['nodes'])) if i not in alias or alias[i] == i]
    new_ids = {old: new for new, old in enumerate(keep)}
    old_to_new = {old: new_ids[alias.get(old, old)] for old in range(len(data['nodes']))}

    def redirect(edges):
        for edge in edges:
            unique = {}
            for dest in edge['destinations']:
                dest['node'] = old_to_new[dest['node']]
                unique[(dest['node'], dest['swap'])] = dest
            edge['destinations'] = [unique[k] for k in sorted(unique)]

    nodes = []
    for old in keep:
        node = data['nodes'][old]
        if node.get('children'):
            redirect(node['children'])
        for piece in node.get('pieces', []):
            redirect(piece['children'])
        if isinstance(node.get('incoming_lineage'), int):
            node['incoming_lineage'] = old_to_new.get(node['incoming_lineage'], node['incoming_lineage'])
        for row in node.get('incoming_origins', []):
            if isinstance(row.get('node'), int):
                row['node'] = old_to_new.get(row['node'], row['node'])
        nodes.append(node)
    data['nodes'] = nodes
    data['roots'] = {name: old_to_new[index] for name, index in data['roots'].items()}
    data = prune(data)

    result = PiecewiseVerifier(data)
    after = result.audit()
    if after['failed_rules']:
        raise ValueError(f'merged graph failed exact audit: {after["failed_rules"][:3]}')
    summary = dict(before_nodes=len(checker.nodes), after_nodes=len(data['nodes']),
                   before_local=len(before['verified_rules']), after_local=len(after['verified_rules']),
                   before_open=len(before['open_nodes']), after_open=len(after['open_nodes']),
                   merged_groups=len(merged_rows),
                   merged_local_nodes=sum(len(r['local_members']) for r in merged_rows),
                   absorbed_open_nodes=sum(len(r['absorbed_open']) for r in merged_rows),
                   proof_hash=after['proof_hash'], groups=merged_rows)
    return data, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('graph', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data, summary = merge(json.loads(args.graph.read_text()))
    checker = PiecewiseVerifier(data)
    try:
        closure = checker.closed()
    except ValueError as error:
        closure = dict(closed=False, reason=str(error))
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    args.output.with_suffix('.audit.json').write_text(json.dumps(checker.audit(), indent=2)+'\n')
    args.output.with_suffix('.closure.json').write_text(json.dumps(closure, indent=2)+'\n')
    args.output.with_suffix('.merge.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(dict(summary={k: v for k, v in summary.items() if k != 'groups'},
                          closure=closure)))


if __name__ == '__main__':
    main()
