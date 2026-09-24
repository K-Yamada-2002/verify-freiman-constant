#!/usr/bin/env python3
"""Remove unreachable parameter values from a selected cyclic cover graph.

Each simultaneous pass retains the initial domains and every incoming image
intersected with its old destination. A rectangular hull of these sets is
an outer bound. No limiting convergence or filledness is assumed.
"""
import argparse
import json
from pathlib import Path

from compact_cyclic_graph import prune
from type_graph_geometry import Cell, root_cells, swapped, transition
from verify_cyclic_types import Verifier


def domains(cell):
    return cell.r, cell.s, cell.ratio


def intersection(a, b):
    result = tuple((max(x[0], y[0]), min(x[1], y[1])) for x, y in zip(a, b))
    return result if all(lo <= hi for lo, hi in result) else None


def contract(checker):
    """One exact, simultaneous reachability contraction, including cycles."""
    incoming = [[] for _ in checker.nodes]
    for name, root in zip(('zero', 'positive'), root_cells()):
        incoming[checker.data['roots'][name]].append(domains(root))
    removed = 0
    for node in checker.nodes:
        cell = checker.cells[node['cell']]
        for edge in node.get('children', []):
            image = transition(cell, *edge['suffixes'], edge['high'])
            retained = []
            for dest in edge['destinations']:
                oriented = swapped(image) if dest['swap'] else image
                target = checker.cells[checker.nodes[dest['node']]['cell']]
                overlap = intersection(domains(oriented), domains(target))
                if overlap is not None:
                    incoming[dest['node']].append(overlap)
                    retained.append(dest)
                else:
                    removed += 1
            edge['destinations'] = retained
    changed = []
    for i, pieces in enumerate(incoming):
        if not pieces:
            continue  # Unreachable nodes are pruned by the caller.
        node = checker.nodes[i]
        old = checker.cells[node['cell']]
        bounds = tuple((min(b[k][0] for b in pieces), max(b[k][1] for b in pieces)) for k in range(3))
        if bounds == domains(old):
            continue
        new = Cell(old.states, old.parity, old.high, *bounds).validate()
        assert intersection(domains(old), bounds) == bounds
        node['cell'] = len(checker.cells)
        checker.cells.append(new)
        checker.data['cells'].append(new.record())
        changed.append(i)
    checker.checked.clear()
    checker.seeds()
    # All formerly valid rules must remain valid, including incoming edges.
    for i, node in enumerate(checker.nodes):
        if node.get('children'):
            checker.local(i)
    return dict(contracted=len(changed), removed_references=removed)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--rounds', type=int, default=4)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    data = json.loads(args.graph.read_text())
    checker = Verifier(data)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('input contains invalid local rules')
    data.setdefault('contraction_sources', []).append(checker.proof_hash())
    for iteration in range(args.rounds):
        summary = contract(checker)
        data.setdefault('contraction_history', []).append(dict(round=iteration, **summary))
        data = prune(data)
        checker = Verifier(data)
        print(json.dumps(dict(round=iteration, nodes=len(checker.nodes), **summary)), flush=True)
        args.output.write_text(json.dumps(data, indent=2)+'\n')
        if not summary['contracted'] and not summary['removed_references']:
            break
    audit = checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    try:
        result = checker.closed()
    except ValueError as error:
        result = dict(status='not closed', reason=str(error))
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
