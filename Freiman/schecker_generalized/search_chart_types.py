#!/usr/bin/env python3
"""Cyclic type search retaining word-induced parameter correlations.

Only routing back to finite base boxes loses information. The last k digits
on each side remain explicit transformations of the same base parameters.
"""
import argparse
from fractions import Fraction as F
from itertools import product
import json
import hashlib
import copy
from pathlib import Path

from chart_geometry import Domain, relative_box
from explore import matrix
from finite_type_game import Game
from search_cyclic_types import Search, fl
from type_graph_geometry import full_labels, root_cells
from verify_chart_types import ChartVerifier


class ChartSearch(Search):
    def __init__(self, labels, chart_memory=1, **kwargs):
        super().__init__(labels, **kwargs)
        self.routing = Search([], states=kwargs.get('states', 6), bins=self.bins, base=self.base,
                              outer_depth=0, local_filter=False)
        self.base_ids = {c: i for i,c in enumerate(self.routing.cells)}
        self.chart_memory = chart_memory
        self.cells, self.floatcells = [], []
        self.domain_ids = {}
        self.state_upgrades = []
        for base in root_cells():
            self.register(Domain(base, ('', ''), base.high))

    def register(self, domain):
        if domain in self.domain_ids:
            return self.domain_ids[domain]
        cid = len(self.cells)
        self.domain_ids[domain] = cid
        self.cells.append(domain)
        outer = domain.outer
        self.floatcells.append((tuple(map(fl, outer.r)), tuple(map(fl, outer.s)),
                                tuple(map(fl, outer.ratio)), tuple(map(fl, outer.anchors()))))
        return cid

    def native_point(self, cid, point):
        result = []
        for word, x in zip(self.cells[cid].words, point):
            a, b, c, d = matrix(word)
            result.append((a*x+b)/(c*x+d))
        return tuple(result)

    def value(self, cid, point):
        domain = self.cells[cid]
        return domain.direction*self.routing.value(self.base_ids[domain.base], self.native_point(cid, point))

    def _ge(self, cid, first, second):
        domain = self.cells[cid]
        a, b = self.native_point(cid, first), self.native_point(cid, second)
        if domain.direction < 0:
            a, b = b, a
        return self.routing.ge(self.base_ids[domain.base], a, b)

    def native_cell(self, cid):
        domain = self.cells[cid]
        return (*self.routing.native_cell(self.base_ids[domain.base]), domain.direction)

    def parameter_samples(self, cid):
        domain = self.cells[cid]
        base_id = self.base_ids[domain.base]
        rb, sb, qb, old_anchors = self.routing.floatcells[base_id]
        middle = tuple(sum(z)/2 for z in (rb, sb, qb))
        points = [middle]
        if self.outer_samples == 3:
            points.extend((middle[0], middle[1], q) for q in qb)
        elif self.outer_samples == 9:
            points.extend(product(rb, sb, qb))
        new_anchors = tuple(map(fl, domain.anchors()))
        result = []
        for r, s, q in points:
            shapes, factors = [], []
            for word, x, old, new in zip(domain.words, (r, s), old_anchors, new_anchors):
                a, b, c, d = matrix(word)
                shapes.append((a*x+c)/(b*x+d))
                factors.append((x*(a*new+b)+c*new+d)/(1+x*old))
            result.append((*shapes, q*(factors[0]/factors[1])**2))
        return result

    def child_candidates(self, cid, u, v, high):
        return next(self.child_routes(cid, u, v, high), (None, None))

    def child_routes(self, cid, u, v, high):
        child = self.cells[cid].extend(u, v, high)
        outer = child.outer
        image = (child.states, child.parity, child.high,
                 tuple(map(fl, outer.r)), tuple(map(fl, outer.s)), tuple(map(fl, outer.ratio)))
        # The distinguished periodic returns retain their exact invariant R.
        for j in dict.fromkeys((1, 0, cid)):
            root = self.cells[j]
            if (child.states, child.parity, child.high) != (root.states, root.parity, root.high):
                continue
            box = relative_box(child, root)
            if box is not None and all(a[0] <= b[0] and b[1] <= a[1] for a,b in zip(
                    (root.base.r, root.base.s, root.base.ratio), (box.r, box.s, box.ratio))):
                yield image, [(j, False)]
        keep, dropped = [], []
        for word in child.words:
            split = max(0, len(word)-self.chart_memory)
            dropped.append(word[:split])
            keep.append(word[split:])
        middle = Domain(child.base, tuple(dropped), child.base.high).outer
        route = (middle.states, middle.parity, middle.high,
                 tuple(map(fl, middle.r)), tuple(map(fl, middle.s)), tuple(map(fl, middle.ratio)))
        targets = self.routing.destinations(route)
        if not targets:
            return
        result = []
        for base_id, swap in targets:
            words = tuple(keep[::-1] if swap else keep)
            h = high if not swap or child.parity > 0 else not high
            target = Domain(self.routing.cells[base_id], words, h).validate()
            result.append((self.register(target), swap))
        yield image, result

    def certificate(self, game):
        result = super().certificate(game)
        result['format'] = 'freiman-chart-types-v1'
        return result

    def snapshot(self, game, configuration, engine_hash):
        return dict(format='freiman-chart-search-state-v1', engine_hash=engine_hash,
                    configuration=configuration, labels=sorted(self.labels),
                    domains=[c.record() for c in self.cells],
                    shape_menu=self.shape_menu, shape_learning=self.shape_learning,
                    state_upgrades=self.state_upgrades, game=game.snapshot())


def engine_hash():
    here = Path(__file__).parent
    names = ('search_chart_types.py', 'search_cyclic_types.py', 'finite_type_game.py', 'chart_geometry.py',
             'type_graph_geometry.py', 'invariant_boxes.py', 'explore.py', 'cyclic_planner.cpp',
             'cover_optimization.py', 'learn_small_type_menu.py', 'adaptive_types.py', 'search_shape_bank.py',
             'verify_chart_types.py', 'verify_cyclic_types.py')
    digest = hashlib.sha256()
    for name in names:
        digest.update(name.encode())
        digest.update((here/name).read_bytes())
    return digest.hexdigest()


def restore_search(state, expected_hash, allow_upgrade=False):
    if state['format'] != 'freiman-chart-search-state-v1':
        raise ValueError('unknown search state format')
    upgrade = state['engine_hash'] != expected_hash
    if upgrade and not allow_upgrade:
        raise ValueError('search engine changed; old failures cannot be resumed unchanged')
    configuration = dict(state['configuration'])
    for name in ('base', 'balance'):
        configuration[name] = F(configuration[name])
    search = ChartSearch(state['labels'], **configuration, shape_menu=state['shape_menu'])
    search.cells, search.floatcells, search.domain_ids = [], [], {}
    for row in state['domains']:
        search.register(Domain.read(row))
    game = Game.restore(state['game'])
    for cid, lo, hi in game.keys:
        if not (0 <= cid < len(search.cells) and 0 <= lo < len(search.points(cid)) and 0 <= hi < len(search.points(cid))):
            raise ValueError('saved point index is invalid')
    search.shape_learning = state['shape_learning']
    search.game = game
    search.state_upgrades = list(state.get('state_upgrades', []))
    if upgrade:
        # Recheck ALL saved positive rules, including unreachable ones that
        # may become reusable again. Keep the two actual A_n roots first.
        all_game = copy.deepcopy(game)
        all_game.roots += [i for i in range(len(game.keys)) if i not in game.roots]
        audit = ChartVerifier(search.certificate(all_game)).audit()
        if audit['failed_rules']:
            raise ValueError('saved positive rules failed upgrade audit')
        game.permanent_rejections.clear()
        reopened = game.forget_rejections()
        game.stop = 'engine upgraded; every negative decision reopened'
        search.state_upgrades.append(dict(previous_hash=state['engine_hash'], new_hash=expected_hash,
                    verified_local_rules=len(audit['verified_rules']), source_proof_hash=audit['proof_hash'],
                    reopened=reopened))
    return search, game


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--chart-memory', type=int, default=1)
    ap.add_argument('--states', type=int, choices=(6, 13), default=6)
    ap.add_argument('--bins', type=int, default=25)
    ap.add_argument('--base', type=F, default=F(22, 25))
    ap.add_argument('--max-step', type=int, default=1)
    ap.add_argument('--outer-depth', type=int, default=3)
    ap.add_argument('--outer-samples', type=int, choices=(1, 3, 9), default=3)
    ap.add_argument('--max-shapes', type=int, default=32)
    ap.add_argument('--seconds', type=float, default=240)
    ap.add_argument('--max-types', type=int, default=12000)
    ap.add_argument('--max-steps', type=int, default=100000)
    ap.add_argument('--depth-first', action='store_true')
    ap.add_argument('--native-executable', type=Path)
    ap.add_argument('--resume-state', type=Path, help='restore all obligations, failures, and queue order')
    ap.add_argument('--upgrade-state', action='store_true',
                    help='on engine changes, exactly recheck saved rules and discard every negative decision')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not (args.chart_memory >= 1 and args.bins > 0 and 0 < args.base < 1 and args.max_step > 0
            and args.outer_depth >= 0 and args.max_shapes >= 2 and args.seconds > 0 and args.max_types >= 2
            and args.max_steps > 0):
        ap.error('invalid finite search bounds')
    fingerprint = engine_hash()
    if args.resume_state:
        state = json.loads(args.resume_state.read_text())
        configuration = dict(state['configuration'])
        search, game = restore_search(state, fingerprint, args.upgrade_state)
    else:
        data = json.loads(Path(__file__).with_name('adaptive_depth8_certificate.json').read_text())
        labels = [z for case in data['cases'] for shape in case['types'] for z in shape]
        configuration = dict(chart_memory=args.chart_memory, states=args.states, bins=args.bins,
                    base=args.base, max_step=args.max_step, outer_depth=args.outer_depth, outer_samples=args.outer_samples,
                    local_filter=False, balance=F(9, 10), reuse_pending=True,
                    adaptive_shapes=True, max_shapes=args.max_shapes)
        search = ChartSearch(labels, **configuration, shape_menu=[full_labels(1), full_labels(-1)])
        game = Game(search.roots(), depth_first=args.depth_first)
        search.game = game
    if args.native_executable:
        search.native_executable = args.native_executable.resolve()
    def checkpoint(game):
        cert = search.certificate(game)
        cert['shape_menu'], cert['shape_learning'] = search.shape_menu, search.shape_learning
        cert['state_upgrades'] = search.state_upgrades
        cert['settings'] = dict(configuration={k: str(v) if isinstance(v, F) else v for k,v in configuration.items()},
                depth_first=game.depth_first, engine_hash=fingerprint,
                resume_state=str(args.resume_state) if args.resume_state else None,
                budgets=dict(seconds=args.seconds, max_types=args.max_types, additional_steps=args.max_steps),
                native_executable=str(args.native_executable) if args.native_executable else None)
        cert['search']['closed_supported_types'] = len(game.supported())
        tmp = args.output.with_suffix('.tmp')
        tmp.write_text(json.dumps(cert, indent=2)+'\n')
        tmp.replace(args.output)
        state = search.snapshot(game, {k: str(v) if isinstance(v, F) else v for k,v in configuration.items()}, fingerprint)
        state_path = args.output.with_suffix('.state.json')
        state_tmp = state_path.with_suffix('.tmp')
        state_tmp.write_text(json.dumps(state, separators=(',', ':'))+'\n')
        state_tmp.replace(state_path)
        print(json.dumps(game.summary()), flush=True)
    checkpoint(game)
    try:
        game.run(search.planner, args.max_types, game.steps+args.max_steps, args.seconds,
                 lambda g: checkpoint(g) if g.steps % 500 == 0 else None)
    except KeyboardInterrupt:
        game.stop = 'interrupted; open obligations retained'
    finally:
        search.close_native()
    checkpoint(game)
    checker = ChartVerifier(json.loads(args.output.read_text()))
    audit = checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    print(json.dumps(dict(local=len(audit['verified_rules']), open=len(audit['open_nodes']), failed=len(audit['failed_rules']))), flush=True)
    try:
        verified = checker.closed()
    except ValueError as error:
        print(json.dumps(dict(closed=False, reason=str(error))), flush=True)
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(verified, indent=2)+'\n')
        print(json.dumps(verified), flush=True)


if __name__ == '__main__':
    main()
