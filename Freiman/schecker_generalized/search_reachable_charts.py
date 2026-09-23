#!/usr/bin/env python3
"""Keep new child obligations close to the incoming image on a fixed grid.

Ordinary routing proposes a family of coarse chart boxes. Intersect
each box with the incoming outer image, then round outwards on that box's fixed
affine dyadic grid. Exact periodic/self returns are retained unchanged.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from chart_geometry import relative_box
from contract_cyclic_domains import domains, intersection
from contract_piecewise_charts import grid_enclosure, restrict
from search_piecewise_charts import (PiecewiseSearch, STATE_FORMAT as BASE_FORMAT,
                                     fingerprint as base_fingerprint, restore as base_restore)
from verify_piecewise_charts import PiecewiseVerifier


STATE_FORMAT = 'freiman-reachable-chart-search-state-v1'


class ReachableSearch(PiecewiseSearch):
    def initialize_routing(self, bits, policy='on_failure'):
        if type(bits) is not int or not 0 <= bits <= 8:
            raise ValueError('incoming grid bits must be between 0 and 8')
        self.reach_grid_bits = bits
        if policy not in ('eager', 'on_failure'):
            raise ValueError('unknown incoming routing policy')
        self.reach_policy, self.refined_cids = policy, set()
        self.reach_statistics = dict(routes=0, tightened_destinations=0,
                                     removed_destinations=0, new_domains=0,
                                     refinement_attempts=0, refinement_recoveries=0, reopened=0)

    def child_routes(self, cid, u, v, high):
        if self.reach_policy == 'on_failure' and cid not in self.refined_cids:
            yield from super().child_routes(cid, u, v, high)
            return
        child = self.cells[cid].extend(u, v, high)
        for image, destinations in super().child_routes(cid, u, v, high):
            # Do not turn an exact return into an endlessly specialized copy
            # of itself. These routes have already passed exact containment.
            if len(destinations) == 1 and destinations[0][0] in (0, 1, cid):
                yield image, destinations
                continue
            if self.reach_policy == 'on_failure':
                # Retain the shared coarse option. Narrower domains are
                # additional alternatives, never replacements for valid reuse.
                yield image, destinations
            result = []
            self.reach_statistics['routes'] += 1
            for j, swap in destinations:
                target = self.cells[j]
                actual = child.exchange() if swap else child
                incoming = relative_box(actual, target)
                if incoming is None:
                    result.append((j, swap))
                    continue
                bounds = intersection(domains(incoming), domains(target.base))
                if bounds is None:
                    self.reach_statistics['removed_destinations'] += 1
                    continue
                rounded = grid_enclosure(bounds, domains(target.base), self.reach_grid_bits)
                if rounded == domains(target.base):
                    result.append((j, swap))
                    continue
                size = len(self.cells)
                k = self.register(restrict(target, rounded))
                self.reach_statistics['new_domains'] += len(self.cells)-size
                self.reach_statistics['tightened_destinations'] += 1
                result.append((k, swap))
            if result and (self.reach_policy == 'eager' or result != destinations):
                yield image, result

    def planner(self, key, rejected):
        proposal = super().planner(key, rejected)
        cid = key[0]
        if (proposal is not None or self.reach_policy != 'on_failure' or cid in self.refined_cids
                or key in self.game.permanent_rejections):
            return proposal
        self.refined_cids.add(cid)
        self.reach_statistics['refinement_attempts'] += 1
        self.moves.cache_clear()
        self.native_geometry.cache_clear()
        self.local_masks.cache_clear()
        self.failed_intervals.pop(cid, None)
        # The route menu for every interval on this domain has expanded.
        # Its previous bounded-search failures must therefore be retried.
        for old, entry in zip(self.game.keys, self.game.entries):
            if old[0] == cid and entry['status'] == 'rejected' and old not in self.game.permanent_rejections:
                entry['status'] = 'pending'
                self.game.add(old)
                self.reach_statistics['reopened'] += 1
        proposal = super().planner(key, rejected)
        self.reach_statistics['refinement_recoveries'] += proposal is not None
        return proposal

    def snapshot(self, game, configuration, fingerprint):
        result = super().snapshot(game, configuration, fingerprint)
        result.update(format=STATE_FORMAT, reach_statistics=self.reach_statistics,
                      refined_cids=sorted(self.refined_cids))
        return result


def fingerprint():
    here = Path(__file__).parent
    return hashlib.sha256(base_fingerprint().encode()+(here/'search_reachable_charts.py').read_bytes()+
                          (here/'contract_piecewise_charts.py').read_bytes()).hexdigest()


def restore(state, bits=2, policy='on_failure'):
    source = copy.deepcopy(state)
    if source['format'] == STATE_FORMAT:
        source['format'] = BASE_FORMAT
        # Earlier snapshots used unconditional specialization.
        policy = source['configuration'].pop('reach_policy', 'eager')
    bits = source['configuration'].pop('reach_grid_bits', bits)
    unchanged = state['engine_hash'] == fingerprint()
    # A changed discovery policy invalidates every negative decision. Existing
    # positive rules are audited by the base importer before being retained.
    source['engine_hash'] = base_fingerprint() if unchanged else 'incoming-routing-upgrade:'+state['engine_hash']
    search, game, config = base_restore(source)
    search.__class__ = ReachableSearch
    search.initialize_routing(bits, policy)
    search.refined_cids = set(state.get('refined_cids', []))
    if not all(type(i) is int and 0 <= i < len(search.cells) for i in search.refined_cids):
        raise ValueError('invalid saved refinement domain')
    search.reach_statistics.update(state.get('reach_statistics', {}))
    if not unchanged:
        search.state_upgrades[-1].update(previous_hash=state['engine_hash'], new_hash=fingerprint(),
                                        operation='incoming image routing on a fixed grid')
    config['reach_grid_bits'] = bits
    config['reach_policy'] = policy
    return search, game, config


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state', type=Path)
    ap.add_argument('--grid-bits', type=int, default=2)
    ap.add_argument('--routing-policy', choices=('on_failure', 'eager'), default='on_failure')
    ap.add_argument('--seconds', type=float, default=180)
    ap.add_argument('--max-steps', type=int, default=1500)
    ap.add_argument('--max-types', type=int, default=6500)
    ap.add_argument('--native-executable', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not 0 <= args.grid_bits <= 8 or args.seconds <= 0 or args.max_steps < 1 or args.max_types < 2:
        ap.error('invalid finite search bounds')
    search, game, config = restore(json.loads(args.state.read_text()), args.grid_bits, args.routing_policy)
    digest = fingerprint()
    if args.native_executable:
        search.native_executable = args.native_executable.resolve()
    def checkpoint(game):
        graph = search.certificate(game)
        graph.update(settings=dict(configuration=config, source_state=str(args.state), engine_hash=digest,
                         budgets=dict(seconds=args.seconds, additional_steps=args.max_steps, max_types=args.max_types)),
                     state_upgrades=search.state_upgrades, reach_statistics=search.reach_statistics)
        graph['search']['closed_supported_types'] = len(game.supported())
        def save(path, data, compact=False):
            temp = path.with_suffix(path.suffix+'.tmp')
            temp.write_text(json.dumps(data, separators=(',', ':') if compact else None,
                                       indent=None if compact else 2)+'\n')
            temp.replace(path)
        save(args.output, graph)
        save(args.output.with_suffix('.state.json'), search.snapshot(game, config, digest), True)
        print(json.dumps(dict(search=game.summary(), incoming=search.reach_statistics,
                              partition=search.partition_statistics)), flush=True)
    checkpoint(game)
    try:
        game.run(search.planner, max_types=args.max_types, max_steps=game.steps+args.max_steps,
                 seconds=args.seconds, checkpoint=lambda g: checkpoint(g) if g.steps % 500 == 0 else None)
    except KeyboardInterrupt:
        game.stop = 'interrupted; open obligations retained'
    finally:
        search.close_native()
    checkpoint(game)
    checker = PiecewiseVerifier(json.loads(args.output.read_text()))
    audit = checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    print(json.dumps(dict(local=len(audit['verified_rules']), open=len(audit['open_nodes']),
                         failed=len(audit['failed_rules']))), flush=True)
    try:
        result = checker.closed()
    except ValueError as error:
        args.output.with_suffix('.verified.json').unlink(missing_ok=True)
        print(json.dumps(dict(closed=False, reason=str(error))), flush=True)
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
