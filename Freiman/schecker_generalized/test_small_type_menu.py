import json
from fractions import Fraction as F
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import random

from explore import Q
from finite_type_game import Game
from learn_small_type_menu import compose, learn, shape_key, template_labels
from search_cyclic_types import Search
from type_graph_geometry import Cell, anchor, endpoint, full_labels, parameters, swapped, transition
from verify_cyclic_types import Verifier
from cover_optimization import minimum_cover_chain
from compact_cyclic_graph import ratio_guard, widen, fold, prune


class SmallMenuTests(unittest.TestCase):
    def test_periodic_endpoint_alias_keeps_the_shared_template_name(self):
        state = ('3', '')
        shape = (('', False, '', True), ('131213', True, '', False))
        points = [endpoint(state, z) for z in shape]
        self.assertEqual(endpoint(state, ('', True, '', False)), points[1])
        self.assertEqual(template_labels(state, *points, [shape]), shape)
    def test_exact_ratio_guard_retains_boundary_equalities(self):
        cell = Cell(('', ''), 1, True, (Q(F(1, 2)),)*2, (Q(F(1, 2)),)*2, (Q(F(1, 4)), Q(4)))
        lo, hi = anchor('', False), anchor('', True)
        a, b = (hi, lo), (lo, hi)
        self.assertEqual(ratio_guard(cell, [(a, b)], cell.ratio), (Q(F(1, 4)), Q(1)))
        self.assertEqual(ratio_guard(cell, [(b, a)], cell.ratio), (Q(1), Q(4)))
        self.assertEqual(ratio_guard(cell, [(a, b), (b, a)], cell.ratio), (Q(1), Q(1)))

    def test_compaction_preserves_open_initial_obligations(self):
        search = Search([], bins=1, outer_depth=0, local_filter=False)
        data = search.certificate(Game(search.roots()))
        checker = Verifier(data)
        self.assertEqual(widen(checker), [])
        self.assertEqual(fold(checker)['changed_edges'], 0)
        result = Verifier(prune(data)).audit()
        self.assertEqual(len(result['open_nodes']), 2)
        self.assertFalse(result['verified_rules'])

    def test_rule_domain_widening_and_folding_replay_exactly(self):
        data = json.loads((Path(__file__).parent/'cyclic_type_search_graph.json').read_text())
        # Retain a small real prefix of the cover graph, making deeper nodes
        # explicit open obligations. The root families are unchanged.
        active, todo = set(), list(data['roots'].values())
        while todo and len(active) < 5:
            i = todo.pop(0)
            if i in active:
                continue
            active.add(i)
            todo.extend(d['node'] for e in data['nodes'][i]['children'] for d in e['destinations'])
        for i,n in enumerate(data['nodes']):
            if i not in active:
                n['children'] = []
        data = prune(data)
        initial_nodes = len(data['nodes'])
        checker = Verifier(data)
        initial = checker.audit()
        self.assertFalse(initial['failed_rules'])
        self.assertGreater(len(initial['verified_rules']), 0)
        widen(checker)
        fold(checker)
        compacted = prune(data)
        self.assertLessEqual(len(compacted['nodes']), initial_nodes)
        audit = Verifier(compacted).audit()
        self.assertFalse(audit['failed_rules'])
        self.assertTrue(audit['open_nodes'])

    def test_minimum_chain_against_exhaustive_enumeration(self):
        rng = random.Random(462)
        for _ in range(100):
            offers = []
            for i in range(8):
                a, b = sorted(rng.sample(range(11), 2))
                offers.append((a, b, (rng.randrange(4), rng.randrange(1, 4), 1)))
            def enumerate_costs(point, cost):
                if point >= 10:
                    return [cost]
                return [answer for lo, hi, w in offers if lo <= point < hi
                        for answer in enumerate_costs(hi, tuple(a+b for a, b in zip(cost, w)))]
            brute = enumerate_costs(0, (0, 0, 0))
            chain = minimum_cover_chain(offers, 0, 10, lambda a, b: a >= b, lambda a: a)
            self.assertEqual(chain is None, not brute)
            if chain is not None:
                self.assertEqual(tuple(sum(offers[i][2][j] for i in chain) for j in range(3)), min(brute))

    def test_cheapest_next_interval_can_give_a_costlier_whole_cover(self):
        offers = [(0, 4, (0, 1, 1)), (4, 10, (4, 4, 1)), (0, 7, (1, 1, 1)), (7, 10, (1, 1, 1))]
        self.assertEqual(minimum_cover_chain(offers, 0, 10, lambda a,b: a >= b, lambda x: x), [2, 3])
    def test_swapped_composition_against_exact_transition(self):
        parent = parameters('32113', '4322')
        first, second = ('1', '1'), ('2', '3')
        for flip in (False, True):
            middle = transition(parent, *first, True)
            if flip:
                middle = swapped(middle)
            result = transition(middle, *second, False)
            combined = compose(first, second, flip)
            high = not result.high if flip and result.parity < 0 else result.high
            direct = transition(parent, *combined, high)
            if flip:
                direct = swapped(direct)
            self.assertEqual(direct, result)

    def test_macro_frequency_ignores_repeated_destination_boxes(self):
        def node(children):
            return dict(cell=0, lower=full_labels(1)[0], upper=full_labels(1)[1], children=children)
        end = dict(node=1, swap=True)
        graph = dict(cells=[dict(states=('', ''), parity=1, high=True)], nodes=[
            node([dict(suffixes=('1', '2'), destinations=[end, end, end])]),
            node([dict(suffixes=('3', '1'), destinations=[dict(node=2, swap=False)])]),
            node([])])
        result = learn([graph], depth=2)
        rules = {tuple(r['suffixes']): r['frequency'] for r in result['macros'][0]['successors']}
        self.assertEqual(rules[('11', '23')], 1)

    def test_forgetting_failure_after_menu_growth_reopens_root(self):
        game = Game([0]).run(lambda *_: None)
        self.assertTrue(game.rejected(0))
        self.assertEqual(game.forget_rejections(), 1)
        self.assertFalse(game.closed())
        game.run(lambda key, _: ('return', [key]))
        self.assertTrue(game.closed())

    @unittest.skipUnless(shutil.which('c++'), 'C++17 compiler unavailable')
    def test_adaptive_small_menu_python_native_exact_replay(self):
        here = Path(__file__).resolve().parent
        data = json.loads((here/'adaptive_depth8_certificate.json').read_text())
        labels = [z for case in data['cases'] for shape in case['types'] for z in shape]
        macro_data = json.loads((here/'small_type_menu12.json').read_text())
        macros = {(tuple(row['states']), row['parity']): [tuple(r['suffixes']) for r in row['successors']]
                  for row in macro_data['macros']}
        outputs = []
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp)/'planner'
            subprocess.run(['c++', '-O2', '-std=c++17', '-ffp-contract=off',
                            str(here/'cyclic_planner.cpp'), '-o', str(binary)], check=True)
            for native in (False, True):
                search = Search(labels, max_step=1, outer_depth=3, local_filter=False,
                    macro_menu=macros, shape_menu=[full_labels(1), full_labels(-1)],
                    adaptive_shapes=True, max_shapes=12, min_cost_cover=True)
                game = Game(search.roots(), depth_first=False)
                search.game = game
                if native:
                    search.native_executable = binary
                try:
                    game.run(search.planner, max_types=500, max_steps=8, seconds=60)
                finally:
                    search.close_native()
                self.assertTrue(search.shape_learning)
                cert = search.certificate(game)
                self.assertFalse(Verifier(cert).audit()['failed_rules'])
                menu = {shape_key(s) for s in search.shape_menu}
                self.assertLessEqual(len(menu), 12)
                self.assertTrue(all(shape_key((n['lower'], n['upper'])) in menu for n in cert['nodes']))
                for n in cert['nodes']:
                    for e in n['children']:
                        self.assertIn(shape_key((e['lower'], e['upper'])), menu)
                outputs.append(cert)
        for key in ('cells', 'nodes', 'roots'):
            self.assertEqual(outputs[0][key], outputs[1][key])


if __name__ == '__main__':
    unittest.main()
