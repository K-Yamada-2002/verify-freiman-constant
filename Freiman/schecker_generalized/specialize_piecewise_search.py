#!/usr/bin/env python3
"""Import a specialized partial graph as explicit new search obligations.

The original complete search state is retained separately. Negative discovery
results on wider domains are not inherited by these different domains.
"""
import argparse
import copy
from fractions import Fraction
import json
from pathlib import Path

from chart_geometry import Domain
from contract_piecewise_charts import edges
from finite_type_game import Game
from search_piecewise_charts import PiecewiseSearch, fingerprint
from type_graph_geometry import endpoint
from verify_piecewise_charts import PiecewiseVerifier


def import_graph(data, source_state):
    checker = PiecewiseVerifier(data)
    before = checker.audit()
    if before['failed_rules']:
        raise ValueError('cannot import invalid local rules')
    config = dict(source_state['configuration'])
    for k in ('base', 'balance'):
        config[k] = Fraction(config[k])
    labels = set(map(tuple, source_state['labels']))
    for node in data['nodes']:
        for row in [node, *edges(node)]:
            labels.update(tuple(row[k]) for k in ('lower', 'upper'))
    search = PiecewiseSearch(labels, **config, shape_menu=source_state['shape_menu'])
    cids = [search.register(d) for d in checker.cells]
    keys = []
    for node in data['nodes']:
        cid = cids[node['cell']]
        lookup = {p[2]: i for i, p in enumerate(search.points(cid))}
        keys.append((cid, *(lookup[endpoint(search.cells[cid].states, node[k])]
                            for k in ('lower', 'upper'))))
    game = Game([keys[data['roots'][name]] for name in ('zero', 'positive')],
                depth_first=source_state['game']['depth_first'])
    search.game = game
    for key in keys:
        game.add(key)
    def convert(plan):
        return [dict(copy.deepcopy(e), destinations=[dict(key=keys[d['node']], swap=d['swap'])
                    for d in e['destinations']]) for e in plan]
    # Equal specialized types may merge. Any one audited local implication
    # suffices, and all its dependencies remain ordinary obligations.
    for i, node in enumerate(data['nodes']):
        if not node.get('children') and not node.get('pieces'):
            continue
        entry = game.entries[game.ids[keys[i]]]
        if entry['status'] == 'local':
            continue
        if node.get('pieces'):
            plan = dict(pieces=[dict(cell=cids[p['cell']], children=convert(p['children']))
                                for p in node['pieces']])
        else:
            plan = convert(node['children'])
        children = list(dict.fromkeys(game.ids[keys[d['node']]] for e in edges(node) for d in e['destinations']))
        entry.update(status='local', plan=plan, children=children)
        for j in children:
            game.entries[j]['parents'].add(game.ids[keys[i]])
    active = game.reachable()
    game.queue.clear()
    game.queued.clear()
    ordered = sorted(active, key=lambda i: (-len(game.entries[i]['parents']), i))
    # add() reverses order in depth-first mode. Preserve the same initial
    # priority in either mode; subsequent parent repair still stays urgent.
    for i in reversed(ordered) if game.depth_first else ordered:
        if game.entries[i]['status'] == 'pending':
            game.add(game.keys[i])
    search.shape_learning = copy.deepcopy(source_state['shape_learning'])
    search.state_upgrades = [dict(operation='import specialized partial strategy',
        source_proof_hash=before['proof_hash'], source_engine_hash=source_state['engine_hash'],
        source_steps=source_state['game']['steps'], source_nodes=len(data['nodes']),
        imported_registered=len(game.keys), inherited_negative_decisions=0,
        contraction_history=data.get('chart_contraction_history', []))]
    after = PiecewiseVerifier(search.certificate(game)).audit()
    if after['failed_rules']:
        raise ValueError('import changed the meaning of local rules')
    return search, game, {k: str(v) if isinstance(v, Fraction) else v for k, v in config.items()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--source-state', type=Path, required=True)
    ap.add_argument('--min-cost-cover', action='store_true', help='minimize additive new-obligation cost for each cover')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    search, game, config = import_graph(json.loads(args.graph.read_text()), json.loads(args.source_state.read_text()))
    if args.min_cost_cover:
        search.min_cost_cover = True
        config['min_cost_cover'] = True
    state = search.snapshot(game, config, fingerprint())
    args.output.write_text(json.dumps(state, separators=(',', ':'))+'\n')
    print(json.dumps(dict(game.summary(), proof_hash=PiecewiseVerifier(search.certificate(game)).proof_hash())), flush=True)


if __name__ == '__main__':
    main()
