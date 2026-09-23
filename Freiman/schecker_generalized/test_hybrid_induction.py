import copy
import json
import unittest
from unittest.mock import patch

from complete_certificate_codec import bits_code
from explore import Q
from hybrid_discovery import Constructive, Mosaic
from search_complete_induction import ExhaustiveStream
from search_hybrid_induction import FairSlices
from search_piecewise_charts import PiecewiseSearch, fingerprint
from specialize_piecewise_search import import_graph
from test_piecewise_charts import split_rule
from test_rule_reuse import clone_open_obligation
from type_graph_geometry import full_labels
from verify_piecewise_charts import PiecewiseVerifier


class FakeClock:
    def __init__(self):
        self.time = 0.

    def __call__(self):
        return self.time


def seed(data):
    from finite_type_game import Game
    search = PiecewiseSearch([], bins=1, outer_depth=0, partition_depth=0,
                             shape_menu=[(n['lower'], n['upper']) for n in data['nodes']])
    game = Game(search.roots())
    search.game = game
    config = dict(bins=1, base='22/25', balance='0', outer_depth=0, partition_depth=0,
                  max_shapes=48, max_step=1)
    source = search.snapshot(game, config, fingerprint())
    search, game, config = import_graph(data, source)
    return search.snapshot(game, config, fingerprint())


class HybridTests(unittest.TestCase):
    def test_slow_unsuccessful_fast_lane_cannot_starve_late_universal_witness(self):
        clock = FakeClock()
        seen, fast_calls = [], []
        def decode(bits):
            index = bits_code(bits)
            seen.append(index)
            clock.time += .11
            return index
        def check(i):
            if i != 73:
                raise ValueError('not a witness')
            return {'proof': i}
        def fast():
            fast_calls.append(True)
            clock.time += 30  # One slow atomic step greatly overruns its slice.
        stream = ExhaustiveStream(decoder=decode, checker=check)
        scheduler = FairSlices(stream, fast, share=.05, quantum=1, clock=clock)
        for _ in range(17):
            self.assertIsNone(scheduler.epoch())
        stream = ExhaustiveStream(json.loads(json.dumps(stream.snapshot())), decode, check)
        scheduler = FairSlices(stream, fast, share=.05, quantum=1, clock=clock)
        winner = None
        while winner is None:
            winner = scheduler.epoch()
        self.assertEqual(seen, list(range(74)))
        self.assertEqual(winner, (73, {'proof': 73}))
        self.assertEqual(len(fast_calls), 73)

    def test_time_allocation_and_fast_success(self):
        clock = FakeClock()
        def decode(bits):
            clock.time += .001
            return {}
        def reject(graph):
            raise ValueError('open')
        def fast():
            clock.time += .005
        stream = ExhaustiveStream(decoder=decode, checker=reject)
        scheduler = FairSlices(stream, fast, share=.05, quantum=1, clock=clock)
        for _ in range(10):
            scheduler.epoch()
        measured = scheduler.seconds['exhaustive']/sum(scheduler.seconds.values())
        self.assertLess(abs(measured-.05), .005)
        scheduler.fast_step = lambda: ({'graph': True}, {'verified': True})
        self.assertEqual(scheduler.epoch(), ({'graph': True}, {'verified': True}))

    def test_exhaustive_resource_error_does_not_skip_candidate(self):
        stream = ExhaustiveStream(decoder=lambda bits: (_ for _ in ()).throw(MemoryError()))
        scheduler = FairSlices(stream, lambda: None)
        with self.assertRaises(MemoryError):
            scheduler.epoch()
        self.assertEqual(stream.next_code, 0)

    def test_real_mosaic_exact_replay_resume_and_no_added_types(self):
        graph, source, index = clone_open_obligation()
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in mosaic search')):
            mosaic = Mosaic(graph)
            # Concentrate on the deliberately copied open obligation.
            mosaic.targets = [index]
            for _ in range(3):
                mosaic.step()
            restored = Mosaic(state=json.loads(json.dumps(mosaic.snapshot())))
            while not mosaic.finished:
                mosaic.step()
            while not restored.finished:
                restored.step()
            self.assertEqual(json.loads(json.dumps(mosaic.snapshot())),
                             json.loads(json.dumps(restored.snapshot())))
            self.assertEqual(mosaic.statistics['accepted'], 1)
            checker = PiecewiseVerifier(mosaic.graph)
            checker.local(index)
            self.assertFalse(checker.audit()['failed_rules'])
            with self.assertRaisesRegex(ValueError, 'unresolved'):
                checker.closed()
        self.assertEqual(len(mosaic.graph['nodes']), len(graph['nodes']))
        self.assertEqual(mosaic.graph['roots'], graph['roots'])

    def test_mosaic_combines_offers_from_different_recipes_and_keeps_alternatives(self):
        # A partial order, not a scalar sort. The first tempting edge leads
        # to a dead end, while three other offers form the required chain.
        from types import SimpleNamespace
        mosaic = Mosaic.__new__(Mosaic)
        domain = SimpleNamespace(states=('x', 'y'), parity=1, high=True)
        node = dict(cell=0, children=[])
        intervals = [((0, 0), (8, 3)), ((0, 0), (4, 4)),
                     ((4, 4), (7, 7)), ((7, 7), (10, 10))]
        mosaic.catalog = [dict(edge={'id': i}) for i in range(4)]
        mosaic.ends = dict(enumerate(intervals))
        mosaic.groups = {(domain.states, 1, True): list(range(4))}
        mosaic.targets, mosaic.position, mosaic.work = [0], 0, None
        mosaic.cache = {}
        mosaic.statistics = dict(edge_trials=0, child_checks=0, child_failures=0,
                                 cache_hits=0, accepted=0, exhausted_targets=0)
        def compare_vectors(domain, a, b, strict=False):
            return all(x > y if strict else x >= y for x, y in zip(a, b))
        mosaic.checker = SimpleNamespace(nodes=[node], checked={},
            node=lambda i: (node, domain, (0, 0), (10, 10)),
            child=lambda domain, edge: None, local=lambda i: None)
        with patch('hybrid_discovery.compare', side_effect=compare_vectors):
            while not mosaic.finished:
                mosaic.step()
        self.assertEqual([e['id'] for e in node['children']], [1, 2, 3])

    def test_constructive_failure_remains_open_and_growing_menu_retries(self):
        graph, _, _ = split_rule()
        lane = Constructive(seed(graph))
        before = lane.game.summary()['unresolved']
        target = lane.todo[0]
        with patch.object(lane.search, 'planner', return_value=None):
            lane.step()
        self.assertEqual(lane.game.entries[target]['status'], 'pending')
        self.assertEqual(lane.game.summary()['unresolved'], before)
        old = dict(lane.config)
        lane.widen()
        self.assertIn(target, lane.todo)
        self.assertGreater(lane.config['partition_depth'], old['partition_depth'])
        self.assertGreater(lane.config['max_shapes'], old['max_shapes'])
        restored = Constructive(state=json.loads(json.dumps(lane.snapshot())))
        self.assertEqual(json.loads(json.dumps(restored.snapshot())),
                         json.loads(json.dumps(lane.snapshot())))

    def test_constructive_rejects_empty_unverified_local_rule(self):
        graph, _, _ = split_rule()
        lane = Constructive(seed(graph))
        target = lane.todo[0]
        with patch.object(lane.search, 'planner', return_value=([], [])):
            lane.step()
        self.assertEqual(lane.game.entries[target]['status'], 'pending')
        self.assertEqual(lane.statistics['exact_rejected'], 1)
        self.assertFalse(PiecewiseVerifier(lane.graph()).audit()['failed_rules'])


if __name__ == '__main__':
    unittest.main()
