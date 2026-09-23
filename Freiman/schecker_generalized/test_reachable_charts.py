import json
import unittest
from unittest.mock import patch

from explore import Q
from finite_type_game import Game
from search_chart_types import ChartSearch
from search_piecewise_charts import PiecewiseSearch, fingerprint as base_fingerprint
from search_reachable_charts import ReachableSearch, fingerprint, restore
from type_graph_geometry import full_labels
from verify_piecewise_charts import FORMAT, PiecewiseVerifier


class ReachableChartTests(unittest.TestCase):
    def test_exact_periodic_return_keeps_the_same_type(self):
        search = ReachableSearch([], bins=1, outer_depth=0, shape_menu=[full_labels(1), full_labels(-1)])
        search.initialize_routing(2)
        before = next(ChartSearch.child_routes(search, 1, '131213', '313121', True))
        after = next(search.child_routes(1, '131213', '313121', True))
        self.assertEqual(before, after)
        self.assertEqual(after[1], [(1, False)])

    def test_rounded_incoming_routes_cover_every_proper_child_exactly(self):
        search = ReachableSearch([], bins=25, outer_depth=0, shape_menu=[full_labels(1), full_labels(-1)])
        search.initialize_routing(2, 'eager')
        count = 0
        # The first digit may stay in an exact root chart. A second digit
        # exercises the lossy generic routing that this policy specializes.
        next_domains = [j for _, ds in search.child_routes(0, '1', '', True) for j, _ in ds]
        for cid in (0, 1, *next_domains):
            parent = search.cells[cid]
            for u, v in [(d, '') for d in '123']+[('', d) for d in '123']:
                for high in (False, True):
                    for _, destinations in search.child_routes(cid, u, v, high):
                        child = parent.extend(u, v, high)
                        lower, upper = full_labels(child.parity)
                        if len(u) % 2:
                            lower, upper = upper, lower
                        data = dict(format=FORMAT, cells=[], nodes=[], roots={})
                        for j, _ in destinations:
                            domain = search.cells[j]
                            lo, hi = full_labels(domain.parity)
                            data['nodes'].append(dict(cell=len(data['cells']), lower=lo, upper=hi, children=[]))
                            data['cells'].append(domain.record())
                        edge = dict(suffixes=(u, v), high=high, lower=lower, upper=upper,
                                    destinations=[dict(node=i, swap=swap) for i, (_, swap) in enumerate(destinations)])
                        checker = PiecewiseVerifier(data)
                        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact route replay')):
                            checker.child(parent, edge)
                        count += 1
        self.assertGreater(count, 0)
        self.assertGreater(search.reach_statistics['tightened_destinations'], 0)

    def test_refinement_is_delayed_until_failure_and_keeps_shared_routes(self):
        search = ReachableSearch([], bins=25, outer_depth=0, shape_menu=[full_labels(1), full_labels(-1)])
        search.initialize_routing(2)
        cid = next(search.child_routes(0, '1', '', True))[1][0][0]
        coarse = list(search.child_routes(cid, '1', '', True))
        self.assertEqual(search.reach_statistics['tightened_destinations'], 0)
        key = (cid, 0, 1)
        search.game = Game([key])
        def propose(k, rejected):
            return ([], []) if cid in search.refined_cids else None
        with patch.object(PiecewiseSearch, 'planner', side_effect=propose):
            self.assertEqual(search.planner(key, search.game.rejected), ([], []))
        self.assertEqual(search.reach_statistics['refinement_attempts'], 1)
        self.assertEqual(search.reach_statistics['refinement_recoveries'], 1)
        refined = list(search.child_routes(cid, '1', '', True))
        self.assertTrue(all(route in refined for route in coarse))
        self.assertGreater(len(refined), len(coarse))

    def test_upgrade_reopens_failures_and_same_engine_resume_is_exact(self):
        search = PiecewiseSearch([], bins=1, outer_depth=0, shape_menu=[full_labels(1), full_labels(-1)])
        game = Game(search.roots())
        search.game = game
        game.reject(game.keys[0])
        config = dict(bins=1, outer_depth=0, base='22/25', balance='0', partition_depth=2)
        source = json.loads(json.dumps(search.snapshot(game, config, base_fingerprint())))
        specialized, again, config = restore(source, bits=2)
        self.assertFalse(again.rejected(again.keys[0]))
        self.assertEqual(specialized.reach_grid_bits, 2)
        specialized.refined_cids.add(1)
        state = json.loads(json.dumps(specialized.snapshot(again, config, fingerprint())))
        recovered, third, recovered_config = restore(state)
        self.assertEqual(recovered_config, config)
        self.assertEqual(recovered.refined_cids, {1})
        self.assertEqual(json.loads(json.dumps(again.snapshot())), json.loads(json.dumps(third.snapshot())))
        self.assertEqual(PiecewiseVerifier(specialized.certificate(again)).proof_hash(),
                         PiecewiseVerifier(recovered.certificate(third)).proof_hash())


if __name__ == '__main__':
    unittest.main()
