import copy
from fractions import Fraction as F
import json
import random
from pathlib import Path
import unittest
from unittest.mock import patch

from compact_cyclic_graph import prune
from contract_cyclic_domains import contract, domains, intersection
from cyclic_frontier_gaps import boundary_labels, discover, value, verify_witness
from explore import Q
from finite_type_game import Game
from resume_cyclic_search import graph_labels
from search_cyclic_types import Search
from solve_known_type_library import LibrarySolver, merge_library
from type_graph_geometry import Cell, encode, endpoint, full_labels
from verify_cyclic_types import Verifier


def small_graph():
    data = json.loads((Path(__file__).parent/'small_type_adaptive_graph.json').read_text())
    keep = set(data['roots'].values())
    for i in tuple(keep):
        keep.update(d['node'] for e in data['nodes'][i]['children'] for d in e['destinations'])
    for i, node in enumerate(data['nodes']):
        if i not in keep:
            node['children'] = []
    return prune(data)


class FrontierRepairTests(unittest.TestCase):
    def test_library_ratio_cover_can_select_different_types_on_slabs(self):
        edge = dict(suffixes=['1', ''], high=True)
        offer = (None, None, edge, ((0.5, 1.0), [(0, False, (0.4, 0.75)),
                 (1, True, (0.75, 1.1)), (2, False, (0.4, 1.1))]))
        self.assertEqual(LibrarySolver.destinations(offer, {0, 1}),
                         [dict(node=0, swap=False), dict(node=1, swap=True)])
        self.assertEqual(LibrarySolver.destinations(offer, {2}), [dict(node=2, swap=False)])
        self.assertIsNone(LibrarySolver.destinations(offer, {0}))
        gapped = (None, None, edge, ((0.5, 1.0), [(0, False, (0.4, 0.7)),
                  (1, False, (0.75, 1.1))]))
        self.assertIsNone(LibrarySolver.destinations(gapped, {0, 1}))

    def test_library_elimination_against_independent_greatest_fixed_point(self):
        rng = random.Random(462)
        for _ in range(100):
            options = [[set(rng.sample(range(8), rng.randrange(1, 4)))
                        for _ in range(rng.randrange(4))] for _ in range(8)]
            expected = set(range(8))
            while True:
                nxt = {i for i in expected if any(children <= expected for children in options[i])}
                if nxt == expected:
                    break
                expected = nxt
            solver = LibrarySolver.__new__(LibrarySolver)
            solver.data = dict(nodes=[dict(children=[]) for _ in range(8)])
            solver.generated = 0
            def plan(i, alive):
                for children in options[i]:
                    if children <= alive:
                        return [dict(destinations=[dict(node=j) for j in sorted(children)])]
                return None
            solver.plan = plan
            class Checker:
                checked = {}
                def local(self, i):
                    return dict(dependencies=[d['node'] for e in solver.data['nodes'][i]['children']
                                              for d in e['destinations']])
            solver.checker = Checker()
            self.assertEqual(set(solver.solve()['supported']), expected)

    def test_merging_identical_libraries_does_not_duplicate_types(self):
        data = small_graph()
        merged, offers = merge_library([data, data])
        self.assertEqual(len(merged['nodes']), len(data['nodes']))
        self.assertFalse(Verifier(merged).audit()['failed_rules'])
        self.assertEqual(sum(map(len, offers.values())),
                         2*sum(len(n['children']) for n in data['nodes']))

    def test_import_preserves_local_rules_and_open_dependencies(self):
        data = small_graph()
        before = Verifier(data).audit()
        search = Search(graph_labels(data), bins=25, outer_depth=0, local_filter=False)
        game = search.import_certificate(data)
        result = Verifier(search.certificate(game)).audit()
        self.assertFalse(result['failed_rules'])
        self.assertEqual(len(result['verified_rules']), len(before['verified_rules']))
        self.assertEqual(len(result['open_nodes']), len(before['open_nodes']))
        self.assertFalse(game.closed())
        self.assertTrue(all(game.entries[i]['status'] == 'pending' for i in game.queue))

    def test_external_counterexample_reopens_its_parent(self):
        game = Game([0], depth_first=False)
        game.run(lambda key, _: (str(key), [key+1]), max_steps=3)
        game.reject(2)
        self.assertEqual(game.entries[2]['status'], 'rejected')
        self.assertEqual(game.entries[1]['status'], 'pending')
        self.assertEqual(game.reachable(), {0, 1})
        self.assertNotIn(2, game.queued)
        self.assertNotIn(2, game.entries[3]['parents'])

    def test_menu_growth_keeps_domain_counterexamples_rejected(self):
        game = Game([0, 1, 2])
        for key in (0, 1, 2):
            game.reject(key, permanent=key != 1)
        self.assertEqual(game.forget_rejections(), 1)
        self.assertEqual([e['status'] for e in game.entries], ['rejected', 'pending', 'rejected'])
        self.assertEqual(list(game.queue), [1])

    def test_domain_contraction_rechecks_all_edges_including_cycles(self):
        data = small_graph()
        checker = Verifier(data)
        initial = checker.audit()
        before = [checker.cells[n['cell']] for n in checker.nodes]
        summary = contract(checker)
        self.assertGreater(summary['contracted'], 0)
        for old, node in zip(before, checker.nodes):
            new = checker.cells[node['cell']]
            self.assertEqual(intersection(domains(old), domains(new)), domains(new))
        audit = checker.audit()
        self.assertFalse(audit['failed_rules'])
        self.assertEqual(len(audit['verified_rules']), len(initial['verified_rules']))
        self.assertEqual(audit['open_nodes'], initial['open_nodes'])
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            checker.closed()

    def test_gap_witness_is_replayed_without_decimals(self):
        search = Search([], bins=1, outer_depth=0, local_filter=False)
        data = search.certificate(Game(search.roots()))
        cell = Cell(('', ''), 1, True, (Q(F(1, 2)),)*2,
                    (Q(F(1, 2)),)*2, (Q(F(1, 1000)),)*2)
        data['cells'].append(cell.record())
        lo, hi = full_labels(1)
        data['nodes'].append(dict(cell=2, lower=lo, upper=hi, children=[]))
        checker = Verifier(data)
        witness = discover(checker, 2, depths=(1,))
        self.assertIsNotNone(witness)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in replay')):
            result = verify_witness(checker, witness)
            boundaries = boundary_labels(checker, witness)
            for key, encoded in zip(('lower', 'upper'), boundaries['values']):
                self.assertEqual(encode(value(cell, (cell.r[0], cell.s[0], cell.ratio[0]),
                                              endpoint(cell.states, boundaries[key]))), encoded)
        self.assertGreater(result['comparisons'], 0)
        forged = copy.deepcopy(witness)
        low = value(cell, (cell.r[0], cell.s[0], cell.ratio[0]), endpoint(cell.states, lo))
        forged['gap'] = [encode(low), encode(low+Q(F(1, 100000)))]
        with self.assertRaisesRegex(ValueError, 'legal cylinder'):
            verify_witness(checker, forged)
        forged = copy.deepcopy(witness)
        forged['parameters'][0] = encode(Q(F(3, 4)))
        with self.assertRaisesRegex(ValueError, 'outside the type domain'):
            verify_witness(checker, forged)


if __name__ == '__main__':
    unittest.main()
