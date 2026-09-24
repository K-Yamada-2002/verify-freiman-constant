#!/usr/bin/env python3
"""Rechoose a parent cover using an exactly replayed point gap.

Gap signatures only prune numerical discovery. The ordinary exact verifier
still checks every accepted rule; all fresh children remain obligations.
Witness certificates are saved with the search state and replayed on resume.
"""
import argparse
import copy
from collections import deque
from functools import lru_cache
import json
from pathlib import Path

from audit_chart_gaps import point_checker, replay
from chart_geometry import Domain, relative_box
from chart_strategy_ranks import report
from cyclic_frontier_gaps import value as point_value, verify_witness
from hybrid_discovery import Constructive
from search_piecewise_charts import fingerprint
from type_graph_geometry import decode, encode, square
from verify_piecewise_charts import PiecewiseVerifier
from verify_cyclic_types import Verifier


def contains_point(domain, cell):
    outer = domain.outer
    if outer == cell:
        return True
    if not isinstance(domain, Domain) or (domain.states, domain.parity, domain.high) != (
            cell.states, cell.parity, cell.high):
        return False
    if not all(a <= x <= b for (a, b), (x, _) in zip(
            (outer.r, outer.s, outer.ratio), (cell.r, cell.s, cell.ratio))):
        return False
    image = relative_box(Domain(cell, ('', ''), cell.high), domain)
    return image is not None and all(a <= lo <= hi <= b for (a, b), (lo, hi) in zip(
        (domain.base.r, domain.base.s, domain.base.ratio),
        (image.r, image.s, image.ratio)))


def bank_entry(checker, row):
    replay(checker, row)
    point = tuple(map(decode, row['base_parameters']))
    local = point_checker(checker, row['node'], point)
    return dict(certificate=local.data, witness=copy.deepcopy(row['witness']))


def equivalent_gaps(cell, low, high):
    """Exact changes of normalization, including orientation under exchange."""
    source = Domain(cell, ('', ''), cell.high)
    seen = set()
    for swap in (False, True):
        base = source.exchange().outer if swap else cell
        factor = cell.parity/cell.ratio[0] if swap else 1
        a, b = sorted((factor*low, factor*high))
        for anchor_high in (False, True):
            target = Domain(base, ('', ''), anchor_high).outer
            r = base.r[0]
            scale = square((1+r*target.anchors()[0])/(1+r*base.anchors()[0]))
            item = target, scale*a, scale*b
            if item not in seen:
                seen.add(item)
                yield (*item, swap)


def install_bank(search, bank):
    matches = []
    for entry in bank:
        local = Verifier(entry['certificate'])
        verify_witness(local, entry['witness'])
        cell = local.cells[entry['certificate']['nodes'][entry['witness']['node']]['cell']]
        low, high = map(decode, entry['witness']['gap'])
        for target, a, b, _ in equivalent_gaps(cell, low, high):
            matches.append(install_filter(search, target, a, b))
    return matches


def known_gap_hits(checker, indices, bank):
    """Exact refutations of requested node intervals by saved point gaps."""
    constraints = []
    for number, entry in enumerate(bank):
        local = Verifier(entry['certificate'])
        verify_witness(local, entry['witness'])
        _, cell, _, _ = local.node(entry['witness']['node'])
        low, high = map(decode, entry['witness']['gap'])
        constraints.extend((number, *variant) for variant in equivalent_gaps(cell, low, high))
    hits = []
    for index in indices:
        _, domain, lower, upper = checker.node(index)
        for number, cell, low, high, swapped in constraints:
            if not contains_point(domain, cell):
                continue
            parameters = cell.r[0], cell.s[0], cell.ratio[0]
            a = max(low, point_value(cell, parameters, lower))
            b = min(high, point_value(cell, parameters, upper))
            if a < b:
                hits.append(dict(node=index, bank_entry=number, exchanged=swapped,
                                 cell=cell.record(), gap=[encode(a), encode(b)]))
                break
    return hits


def install_filter(search, cell, low, high):
    if not low < high:
        raise ValueError('nonempty gap required')
    base = search.outer_memberships
    matched = set()
    boxes = (cell.r, cell.s, cell.ratio)
    if any(a != b for a, b in boxes):
        raise ValueError('singleton gap geometry required')
    parameters = tuple(a for a, _ in boxes)

    @lru_cache(None)
    def memberships(cid):
        old = base(cid)
        if not contains_point(search.cells[cid], cell):
            return old
        matched.add(cid)
        groups, result = {}, []
        for point, signature in zip(search.points(cid), old):
            # ChartSearch.value uses the base chart's affine normalization.
            # Witnesses use the transformed cell's normalization instead.
            value = point_value(cell, parameters, point[2])
            region = 0 if value <= low else (1 if value >= high else -1)
            result.append(-1 if signature < 0 or region < 0 else
                          groups.setdefault((signature, region), len(groups)))
        return tuple(result)

    search.outer_memberships = memberships
    search.moves.cache_clear()
    search.native_geometry.cache_clear()
    return matched


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state', type=Path)
    ap.add_argument('gap', type=Path, help='JSON with source_hash and gap fields')
    ap.add_argument('--root', choices=('zero', 'positive'), default='zero')
    ap.add_argument('--node', type=int, help='parent index in restored certificate; overrides --root')
    ap.add_argument('--max-step', type=int, default=3)
    ap.add_argument('--max-shapes', type=int, default=192)
    ap.add_argument('--native-executable', type=Path)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    saved = json.loads(args.state.read_text())
    lane = Constructive(saved)
    source = lane.graph()
    checker = PiecewiseVerifier(source)
    witness = json.loads(args.gap.read_text())
    if witness['source_hash'] != checker.proof_hash():
        raise ValueError('witness source does not match restored graph')
    row = witness['gap']
    replay(checker, row)
    search = lane.search
    search.max_step, search.max_shapes = args.max_step, args.max_shapes
    lane.config.update(max_step=args.max_step, max_shapes=args.max_shapes)
    bank = copy.deepcopy(saved.get('gap_filter_bank', []))
    entry = bank_entry(checker, row)
    if entry not in bank:
        bank.append(entry)
    matches = install_bank(search, bank)
    if args.native_executable:
        search.native_executable = args.native_executable.resolve()
    index = source['roots'][args.root] if args.node is None else args.node
    if not 0 <= index < len(source['nodes']):
        raise ValueError('invalid parent index')
    root = sorted(lane.game.reachable())[index]
    previous = copy.deepcopy(lane.game.entries[root])
    lane.game.entries[root]['status'] = 'pending'
    lane.todo, lane.queued = deque([root]), {root}
    lane.attempted.discard(root)
    try:
        lane.step()
    finally:
        search.close_native()
    accepted = lane.game.entries[root]['status'] == 'local'
    if not accepted:
        for child in lane.game.entries[root]['children']:
            lane.game.entries[child]['parents'].discard(root)
        lane.game.entries[root] = previous
        for child in previous['children']:
            lane.game.entries[child]['parents'].add(root)
    graph = lane.graph()
    final_checker = PiecewiseVerifier(graph)
    audit = final_checker.audit()
    if audit['failed_rules']:
        raise ValueError('repaired graph failed exact audit')
    indices = {node: i for i, node in enumerate(sorted(lane.game.reachable()))}
    hits = known_gap_hits(final_checker,
                         [indices[j] for j in lane.game.entries[root]['children']], bank)
    summary = dict(repaired=accepted and not hits, local_rule_accepted=accepted,
                   known_refuted_children=hits, matched_cells=[sorted(m) for m in matches],
                   statistics=lane.statistics, ranks=report(graph),
                   filter_persisted_in_state=True)
    state = search.snapshot(lane.game, lane.config, fingerprint())
    state['gap_filter_bank'] = bank
    for path, data in (
        (args.output, graph),
        (args.output.with_suffix('.audit.json'), audit),
        (args.output.with_suffix('.report.json'), summary),
        (args.output.with_suffix('.state.json'), state),
    ):
        path.write_text(json.dumps(data, separators=(',', ':'))+'\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
