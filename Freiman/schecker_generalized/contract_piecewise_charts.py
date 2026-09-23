#!/usr/bin/env python3
"""Specialize a partial chart strategy to its exact incoming obligations.

This is a finite, simultaneous outer approximation, including on cycles.
Every seed and every incoming image is retained. Parameter guards are clipped
with their parent. Open intervals remain open, and all rules are replayed.
"""
import argparse
import copy
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from chart_geometry import Domain, relative_box
from contract_cyclic_domains import domains, intersection
from explore import state_of
from type_graph_geometry import Cell, root_cells
from verify_cyclic_types import cover_parameter_box
from verify_piecewise_charts import PiecewiseVerifier


def rules(node):
    if node.get('pieces'):
        return node['pieces']
    return [dict(cell=node['cell'], children=node.get('children', []))]


def edges(node):
    return (edge for rule in rules(node) for edge in rule['children'])


def restrict(domain, bounds):
    base = domain.base
    return Domain(Cell(base.states, base.parity, base.high, *bounds),
                  domain.words, domain.high).validate()


def select_destinations(checker, child, edge):
    """Keep a certified covering chart group, dropping irrelevant targets.

    The verifier requires one common inverse chart to cover the whole child.
    Destinations from other groups cannot be necessary for that certificate.
    No unverified mixing of individually noncovering chart groups is used.
    """
    groups = defaultdict(list)
    for dest in edge['destinations']:
        target = checker.cells[checker.nodes[dest['node']]['cell']]
        original = target.exchange() if dest['swap'] else target
        signature = (original.words, tuple(map(state_of, original.base.states)),
                     original.base.parity, original.base.high)
        groups[signature].append((dest, original))
    choices = []
    for group in groups.values():
        image = relative_box(child, group[0][1])
        if image is None:
            continue
        retained = [(dest, domain) for dest, domain in group
                    if intersection(domains(image), domains(domain.base)) is not None]
        try:
            cover_parameter_box(domains(image), [domains(d.base) for _, d in retained])
        except ValueError:
            continue
        choices.append([dest for dest, _ in retained])
    if not choices:
        raise ValueError('no verified incoming chart cover')
    return min(choices, key=lambda ds: (len(ds), tuple(d['node'] for d in ds)))


def grid_enclosure(bounds, frame, bits):
    """Round outwards on a fixed affine dyadic grid, using exact comparisons.

    Each endpoint can change at most 2**bits times on this frame. In a fixed
    finite strategy this removes the need to assume convergence of endlessly
    shrinking rational/irrational bounds. Rounding only enlarges the incoming
    enclosure; the following intersection keeps it inside the previous domain.
    """
    divisions = 1 << bits
    result = []
    for (lo, hi), (a, b) in zip(bounds, frame):
        if not a <= lo <= hi <= b:
            raise ValueError('incoming interval escapes its fixed grid frame')
        if a == b:
            result.append((a, b))
            continue
        def at(k):
            return a+(b-a)*Fraction(k, divisions)
        def floor(x):
            left, right = 0, divisions
            while left < right:
                middle = (left+right+1)//2
                if at(middle) <= x:
                    left = middle
                else:
                    right = middle-1
            return left
        lower, upper = floor(lo), floor(hi)
        if at(upper) != hi:
            upper += 1
        result.append((at(lower), at(upper)))
    return tuple(result)


def contract(checker, grid_bits=None):
    """One simultaneous pass; caller must supply a locally audited graph."""
    incoming = [[] for _ in checker.nodes]
    for name, root in zip(('zero', 'positive'), root_cells()):
        index = checker.data['roots'][name]
        target = checker.cells[checker.nodes[index]['cell']]
        image = relative_box(Domain(root, ('', ''), root.high), target)
        if image is None:
            raise ValueError('seed has no incoming chart image')
        incoming[index].append(domains(image))
    removed = 0
    # Read every source before changing any destination: this is a
    # simultaneous sound outer bound, not an assumption of convergence.
    for node in checker.nodes:
        for rule in rules(node):
            parent = checker.cells[rule['cell']]
            for edge in rule['children']:
                child = parent.extend(*edge['suffixes'], edge['high'])
                chosen = select_destinations(checker, child, edge)
                removed += len(edge['destinations'])-len(chosen)
                edge['destinations'] = chosen
                for dest in chosen:
                    target = checker.cells[checker.nodes[dest['node']]['cell']]
                    actual = child.exchange() if dest['swap'] else child
                    image = relative_box(actual, target)
                    if image is None:
                        raise ValueError('selected inverse chart unexpectedly failed')
                    overlap = intersection(domains(image), domains(target.base))
                    if overlap is None:
                        raise ValueError('selected destination has empty incoming image')
                    incoming[dest['node']].append(overlap)
    changed, piece_changes, simplified = [], 0, 0
    def append(domain):
        index = len(checker.cells)
        checker.cells.append(domain)
        checker.data['cells'].append(domain.record())
        return index
    for i, boxes in enumerate(incoming):
        if not boxes:
            continue  # Pruned if unreachable from the seeds.
        node = checker.nodes[i]
        old = checker.cells[node['cell']]
        bounds = tuple((min(b[k][0] for b in boxes), max(b[k][1] for b in boxes)) for k in range(3))
        if intersection(domains(old.base), bounds) != bounds:
            raise ValueError('contraction attempted to enlarge a domain')
        if grid_bits is not None:
            frame = Domain.read(node.setdefault('contraction_frame', old.record()))
            bounds = intersection(domains(old.base), grid_enclosure(bounds, domains(frame.base), grid_bits))
        if bounds == domains(old.base):
            continue
        new = restrict(old, bounds)
        node['cell'] = append(new)
        changed.append(i)
        if node.get('pieces'):
            retained = []
            for piece in node['pieces']:
                part = checker.cells[piece['cell']]
                clipped = intersection(bounds, domains(part.base))
                if clipped is None:
                    piece_changes += 1
                    continue
                if clipped != domains(part.base):
                    piece['cell'] = append(restrict(part, clipped))
                    piece_changes += 1
                retained.append(piece)
            if not retained:
                raise ValueError('contraction lost all guards of a nonempty domain')
            node['pieces'] = retained
            if len(retained) == 1 and checker.cells[retained[0]['cell']] == new:
                node['children'] = retained[0]['children']
                del node['pieces']
                simplified += 1
    checker.checked.clear()
    checker.seeds()
    for i, node in enumerate(checker.nodes):
        if node.get('children') or node.get('pieces'):
            checker.local(i)
    return dict(contracted=len(changed), removed_references=removed,
                clipped_pieces=piece_changes, simplified_rules=simplified)


def prune(data):
    reached, todo = set(), list(data['roots'].values())
    while todo:
        i = todo.pop()
        if i in reached:
            continue
        reached.add(i)
        todo.extend(d['node'] for e in edges(data['nodes'][i]) for d in e['destinations'])
    ordered = sorted(reached)
    ids = {old: new for new, old in enumerate(ordered)}
    used = sorted({row['cell'] for i in ordered
                   for row in [data['nodes'][i], *data['nodes'][i].get('pieces', [])]})
    cids = {old: new for new, old in enumerate(used)}
    nodes = []
    for i in ordered:
        node = copy.deepcopy(data['nodes'][i])
        for row in [node, *node.get('pieces', [])]:
            row['cell'] = cids[row['cell']]
        for edge in edges(node):
            for dest in edge['destinations']:
                dest['node'] = ids[dest['node']]
        nodes.append(node)
    result = dict(data, nodes=nodes, cells=[data['cells'][i] for i in used],
                  roots={k: ids[i] for k, i in data['roots'].items()})
    # These describe historical search obligations, not the specialized graph.
    result.pop('search', None)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--rounds', type=int, default=4)
    ap.add_argument('--grid-bits', type=int, help='fixed affine dyadic grid; omission keeps exact incoming extrema')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.rounds < 1 or (args.grid_bits is not None and not 0 <= args.grid_bits <= 16):
        ap.error('rounds must be positive and grid bits must be between 0 and 16')
    data = json.loads(args.graph.read_text())
    checker = PiecewiseVerifier(data)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('input has invalid local rules')
    print(json.dumps(dict(input_nodes=len(data['nodes']), verified_local=len(audit['verified_rules']))), flush=True)
    data.setdefault('chart_contraction_sources', []).append(dict(path=str(args.graph), proof_hash=checker.proof_hash()))
    for i, node in enumerate(data['nodes']):
        node.setdefault('contraction_source_node', i)
    for iteration in range(args.rounds):
        summary = contract(checker, args.grid_bits)
        data.setdefault('chart_contraction_history', []).append(dict(round=iteration, grid_bits=args.grid_bits, **summary))
        data = prune(data)
        checker = PiecewiseVerifier(data)
        print(json.dumps(dict(round=iteration, nodes=len(checker.nodes), **summary)), flush=True)
        temporary = args.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(data, indent=2)+'\n')
        temporary.replace(args.output)
        if not summary['contracted'] and not summary['removed_references']:
            break
    audit = checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    try:
        result = checker.closed()
    except ValueError as error:
        result = dict(status='not closed', reason=str(error))
    print(json.dumps(dict(nodes=len(checker.nodes), local=len(audit['verified_rules']),
                         open=len(audit['open_nodes']), failed=len(audit['failed_rules']), closure=result)), flush=True)


if __name__ == '__main__':
    main()
