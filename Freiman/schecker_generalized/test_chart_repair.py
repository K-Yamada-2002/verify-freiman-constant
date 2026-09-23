import json
from pathlib import Path
import unittest
from unittest.mock import patch

from finite_type_game import Game
from repair_chart_menu import install_rule, isolated_proposal, repair, select_bundles
from search_chart_types import ChartSearch
from type_graph_geometry import full_labels


class ChartRepairTests(unittest.TestCase):
    def test_shape_budget_never_accepts_a_partial_bundle(self):
        self.assertEqual(select_bundles([{'a','b'}], 1), set())
        selected = select_bundles([{'a','b'}, {'b','c'}, {'a'}], 2)
        self.assertLessEqual(len(selected), 2)
        self.assertEqual(sum(r <= selected for r in ({'a','b'}, {'b','c'}, {'a'})), 2)

    def test_install_retains_open_dependencies_and_parent_links(self):
        game = Game([('root',)], depth_first=False)
        game.add(('old',))
        install_rule(game, ('root',), ([dict(key=('old',))], [('old',)]))
        install_rule(game, ('root',), ([dict(key=('new',))], [('new',)]))
        self.assertFalse(game.closed())
        self.assertNotIn(0, game.entries[game.ids[('old',)]]['parents'])
        self.assertIn(0, game.entries[game.ids[('new',)]]['parents'])
        self.assertEqual(game.entries[game.ids[('new',)]]['status'], 'pending')

    def test_install_does_not_silently_reuse_a_rejected_dependency(self):
        game = Game([('root',)])
        game.add(('child',)); game.reject(('child',))
        before = game.snapshot()
        self.assertFalse(install_rule(game, ('root',), ([dict(key=('child',))], [('child',)])))
        self.assertEqual(game.snapshot(), before)

    def test_probe_restores_discovery_context_after_an_exception(self):
        search = ChartSearch([], chart_memory=1, bins=1, outer_depth=0,
                             shape_menu=[full_labels(1),full_labels(-1)])
        game = Game(search.roots()); search.game = game
        menu = search.shape_menu
        before = game.snapshot()
        with patch.object(search, '_plan_once', side_effect=RuntimeError('probe failed')):
            with self.assertRaisesRegex(RuntimeError, 'probe failed'):
                isolated_proposal(search, game.keys[0], True)
        self.assertIs(search.game, game)
        self.assertEqual(search.shape_menu, menu)
        self.assertEqual(game.snapshot(), before)

    def test_exact_gate_rejects_an_empty_suffix_cycle(self):
        search = ChartSearch([], chart_memory=1, bins=1, outer_depth=0,
                             shape_menu=[full_labels(1),full_labels(-1)])
        game = Game(search.roots()); search.game = game
        key = game.keys[0]; game.reject(key)
        lower,upper = full_labels(search.cells[key[0]].parity)
        edge = dict(suffixes=('',''),high=search.cells[key[0]].high,lower=lower,upper=upper,
                    destinations=[dict(key=key,swap=False)])
        with patch('repair_chart_menu.isolated_proposal', return_value=([edge],[key])):
            result = repair(search, game, probe_count=1, new_shapes=4, seconds=60)
        self.assertEqual(result['probes'][0]['status'], 'exact_rule_rejected')
        self.assertEqual(result['event']['installed'], 0)
        self.assertTrue(game.rejected(key))


if __name__ == '__main__':
    unittest.main()
