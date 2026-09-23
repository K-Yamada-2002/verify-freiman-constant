#!/usr/bin/env python3
"""Batch endpoint-template repairs, with exact replay of every proposed rule.

Probe failures without inheriting negative conclusions about their children.
A proposal is a local rule, never a filling assertion. Select whole bundles
of new shapes, reopen old menu failures once, and retain every dependency.
"""
import argparse
from collections import defaultdict
import copy
import json
from pathlib import Path
import time

from explore import state_of
from finite_type_game import Game
from learn_small_type_menu import shape_key, template_labels
from search_chart_types import engine_hash, restore_search
from type_graph_geometry import endpoint, exchange
from verify_chart_types import ChartVerifier


def isolated_proposal(search, key, unrestricted):
    old = (search.game, search.shape_menu, search.reuse_index,
           search.indexed_keys, search.failed_intervals)
    search.game = Game([key])
    search.reuse_index, search.indexed_keys = defaultdict(list), 0
    search.failed_intervals = defaultdict(list)
    if unrestricted:
        search.shape_menu = None
    search.native_geometry.cache_clear()
    try:
        return search._plan_once(key, search.game.rejected)
    finally:
        (search.game, search.shape_menu, search.reuse_index,
         search.indexed_keys, search.failed_intervals) = old
        search.native_geometry.cache_clear()


def normalize_proposal(search, key, proposal):
    """Do not count a state's alternative names for a known pair as new."""
    edges, dependencies = copy.deepcopy(proposal)
    missing = set()
    for edge in edges:
        states = tuple(state_of(s+w) for s,w in zip(search.cells[key[0]].states, edge['suffixes']))
        points = [endpoint(states, edge[k]) for k in ('lower', 'upper')]
        try:
            edge['lower'], edge['upper'] = template_labels(states, *points, search.shape_menu)
        except ValueError:
            missing.add(shape_key((edge['lower'], edge['upper'])))
    return (edges, dependencies), missing


def proposal_certificate(search, key, proposal):
    edges, children = proposal
    keys = list(dict.fromkeys([key]+list(children)))
    ids = {k:i for i,k in enumerate(keys)}
    cids = list(dict.fromkeys(k[0] for k in keys))
    cell_ids = {c:i for i,c in enumerate(cids)}
    nodes = []
    for cid,lo,hi in keys:
        points = search.points(cid)
        nodes.append(dict(cell=cell_ids[cid], lower=points[lo][1], upper=points[hi][1], children=[]))
    nodes[0]['children'] = [dict(e, destinations=[dict(node=ids[d['key']], swap=d['swap'])
                          for d in e['destinations']]) for e in edges]
    # roots is intentionally empty: this proves only a local implication.
    return dict(format='freiman-chart-types-v1', cells=[search.cells[i].record() for i in cids],
                nodes=nodes, roots={})


def select_bundles(requirements, budget):
    """Greedy set-union budget, enabling a proposal only with its WHOLE set.

    Maximizes the immediate number of newly enabled proposals per added
    shape. This is a heuristic, not a claim of global minimum type count.
    """
    requirements = [set(r) for r in requirements]
    selected = set()
    while True:
        choices = {frozenset(r-selected) for r in requirements if r-selected and len(r|selected) <= budget}
        if not choices:
            return selected
        def score(bundle):
            gain = sum(bool(r-selected) and r <= selected|bundle for r in requirements)
            return (gain/len(bundle), gain, -len(bundle), tuple(sorted(bundle)))
        best = max(choices, key=score)
        selected.update(best)


def install_rule(game, key, proposal):
    """Install an exactly checked local rule; children remain obligations."""
    edges, children = proposal
    if any(k in game.permanent_rejections or game.rejected(k) for k in children):
        return False
    i = game.add(key)
    entry = game.entries[i]
    for j in entry['children']:
        game.entries[j]['parents'].discard(i)
    if i in game.queued:
        game.queue.remove(i)
        game.queued.remove(i)
    entry.update(status='local', children=[], plan=edges)
    child_ids = list(dict.fromkeys(game.add(k) for k in children))
    entry['children'] = child_ids
    for j in child_ids:
        game.entries[j]['parents'].add(i)
    return True


def repair(search, game, probe_count, new_shapes, seconds):
    deadline = time.monotonic()+seconds
    rejected = [i for i,e in enumerate(game.entries) if e['status']=='rejected'
                and game.keys[i] not in game.permanent_rejections]
    rejected.sort(key=lambda i: (-len(game.entries[i]['parents']), i))
    records, proposals, requirements = [], [], []
    for i in rejected[:probe_count]:
        if time.monotonic() >= deadline:
            break
        key = game.keys[i]
        proposal = isolated_proposal(search, key, False)
        status = 'existing_shapes_suffice_with_open_children'
        if proposal is None:
            status = 'new_shapes_required'
            proposal = isolated_proposal(search, key, True)
        row = dict(type=i, key=key, incoming=len(game.entries[i]['parents']), status=status)
        if proposal is None:
            row['status'] = 'no_rule_found_with_unrestricted_shapes'
        else:
            proposal, missing = normalize_proposal(search, key, proposal)
            cert = proposal_certificate(search, key, proposal)
            checker = ChartVerifier(cert)
            try:
                checker.local(0)
            except ValueError as error:
                row.update(status='exact_rule_rejected', reason=str(error))
            else:
                row.update(missing=sorted(missing), local_certificate=cert, proof_hash=checker.proof_hash())
                proposals.append((key, proposal, len(records)))
                requirements.append(missing)
        records.append(row)
        if len(records)%10 == 0:
            print(json.dumps(dict(probed=len(records), exact_local_proposals=len(proposals))), flush=True)
    selected = select_bundles(requirements, new_shapes)
    known = {shape_key(s) for s in search.shape_menu}
    selected -= known
    search.shape_menu = tuple(dict.fromkeys(search.shape_menu+tuple(
        shape for pair in sorted(selected) for shape in (pair, tuple(exchange(z) for z in pair)))))
    search.max_shapes = max(search.max_shapes, len(known|selected))
    search.shape_pairs.cache_clear()
    search.native_geometry.cache_clear()
    search.failed_intervals.clear()
    reopened = game.forget_rejections() if selected else 0
    installed = 0
    for (key, proposal, record), missing in zip(proposals, requirements):
        if missing <= selected:
            ok = install_rule(game, key, proposal)
            records[record]['installed'] = ok
            installed += ok
    event = dict(method='batch exact local proposals', probed=len(records), added=sorted(selected),
                 total=len(known|selected), reopened=reopened, installed=installed)
    search.shape_learning.append(event)
    game.stop = 'batch menu repair; all unproved dependencies retained'
    return dict(status='local rule repair only; no filling assertion', event=event, probes=records)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state', type=Path)
    ap.add_argument('--probes', type=int, default=40)
    ap.add_argument('--new-shapes', type=int, default=12)
    ap.add_argument('--seconds', type=float, default=180)
    ap.add_argument('--native-executable', type=Path)
    ap.add_argument('--output', type=Path, required=True, help='new complete search-state JSON')
    args = ap.parse_args()
    if args.probes <= 0 or args.new_shapes < 0 or args.seconds <= 0:
        ap.error('invalid repair budget')
    state = json.loads(args.state.read_text())
    search,game = restore_search(state, engine_hash())
    if args.native_executable:
        search.native_executable = args.native_executable.resolve()
    try:
        result = repair(search, game, args.probes, args.new_shapes, args.seconds)
    finally:
        search.close_native()
    configuration = dict(state['configuration'], max_shapes=search.max_shapes)
    args.output.write_text(json.dumps(search.snapshot(game, configuration, engine_hash()), separators=(',',':'))+'\n')
    graph = search.certificate(game)
    graph['shape_menu'] = search.shape_menu
    graph['shape_learning'] = search.shape_learning
    checker = ChartVerifier(graph)
    audit = checker.audit()
    if audit['failed_rules']:
        raise ValueError('repaired graph failed exact audit')
    args.output.with_suffix('.graph.json').write_text(json.dumps(graph,indent=2)+'\n')
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    result.update(source_state=str(args.state), configuration=configuration,
                  summary=game.summary(), supported=len(game.supported()))
    args.output.with_suffix('.report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(event=result['event'], summary=game.summary(), supported=len(game.supported()))), flush=True)


if __name__ == '__main__':
    main()
