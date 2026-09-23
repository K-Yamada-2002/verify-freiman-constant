import copy
import json
from fractions import Fraction
from pathlib import Path
import unittest
from unittest.mock import patch

from contract_cyclic_domains import domains, intersection
from contract_piecewise_charts import contract, edges, grid_enclosure, prune, restrict
from explore import Q
from finite_type_game import Game
from search_piecewise_charts import PiecewiseSearch, fingerprint, restore
from specialize_piecewise_search import import_graph
from test_piecewise_charts import split_rule
from type_graph_geometry import full_labels
from verify_piecewise_charts import PiecewiseVerifier


class ChartContractionTests(unittest.TestCase):
    def test_fixed_grid_encloses_irrational_bounds_exactly(self):
        frame = ((Q(0), Q(1)),)*3
        bounds = ((Q(Fraction(1, 100)), Q(Fraction(3, 5))),
                  (Q(0, Fraction(1, 100)), Q(0, Fraction(1, 50))),
                  (Q(Fraction(1, 4)), Q(Fraction(1, 4))))
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in grid rounding')):
            result = grid_enclosure(bounds, frame, 2)
        self.assertEqual(result, ((Q(0), Q(Fraction(3, 4))),
                                  (Q(0), Q(Fraction(1, 2))),
                                  (Q(Fraction(1, 4)), Q(Fraction(1, 4)))))
        self.assertEqual(intersection(result, bounds), bounds)

    def test_fixed_grid_contraction_replays(self):
        data, _, _ = split_rule()
        checker = PiecewiseVerifier(data)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in grid contraction')):
            contract(checker, grid_bits=2)
            frames = [n.get('contraction_frame') for n in checker.nodes]
            contract(checker, grid_bits=2)
            self.assertEqual(frames, [n.get('contraction_frame') for n in checker.nodes])
        self.assertFalse(checker.audit()['failed_rules'])

    def test_simultaneous_contraction_keeps_roots_rules_and_open_obligations(self):
        data, _, _ = split_rule()
        checker = PiecewiseVerifier(data)
        before = checker.audit()
        old = [checker.cells[n['cell']] for n in checker.nodes]
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in contraction')):
            result = contract(checker)
            for prior, node in zip(old, checker.nodes):
                new = checker.cells[node['cell']]
                self.assertEqual(intersection(domains(prior.base), domains(new.base)), domains(new.base))
            after = PiecewiseVerifier(prune(data)).audit()
        self.assertGreater(result['contracted'], 0)
        self.assertFalse(after['failed_rules'])
        self.assertEqual(len(before['verified_rules']), len(after['verified_rules']))
        self.assertTrue(after['open_nodes'])
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            PiecewiseVerifier(prune(data)).closed()

    def test_correlated_piece_guards_survive_contraction(self):
        # Keep the real two-guard example with its open children, plus the
        # actual roots as open obligations. The example is tested even though
        # it is not reached from those roots in this deliberately small graph.
        record = json.loads(Path(__file__).with_name('piecewise_chart_example.json').read_text())
        data = record['certificate']
        s = PiecewiseSearch([], bins=1, outer_depth=0, shape_menu=[full_labels(1), full_labels(-1)])
        root = s.certificate(Game(s.roots()))
        shift = len(data['nodes'])
        cells = len(data['cells'])
        for node in root['nodes']:
            node['cell'] += cells
        data['nodes'].extend(root['nodes'])
        data['cells'].extend(root['cells'])
        data['roots'] = {k: i+shift for k, i in root['roots'].items()}
        checker = PiecewiseVerifier(data)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in contraction')):
            contract(checker)
            result = checker.local(0)
        self.assertEqual(result['parameter_pieces'], 2)

    def test_empty_inverse_cover_is_rejected(self):
        data, _, _ = split_rule()
        next(edges(next(n for n in data['nodes'] if n.get('children') or n.get('pieces'))))['destinations'] = []
        with self.assertRaisesRegex(ValueError, 'no verified incoming chart cover'):
            contract(PiecewiseVerifier(data))

    def test_incoming_shrink_clips_nonroot_parameter_pieces(self):
        data, _, _ = split_rule()
        checker = PiecewiseVerifier(data)
        node = data['nodes'][2]
        parent = checker.cells[node['cell']]
        bounds = list(domains(parent.base))
        axis = next(k for k, (a, b) in enumerate(bounds) if a != b)
        a, b = bounds[axis]
        midpoint = (a+b)/2
        node['pieces'] = []
        for interval in ((a, midpoint), (midpoint, b)):
            part = list(bounds)
            part[axis] = interval
            node['pieces'].append(dict(cell=len(data['cells']), children=copy.deepcopy(node['children'])))
            data['cells'].append(restrict(parent, tuple(part)).record())
        node['children'] = []
        checker = PiecewiseVerifier(data)
        self.assertFalse(checker.audit()['failed_rules'])
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in piece clipping')):
            result = contract(checker)
            self.assertGreater(result['clipped_pieces'], 0)
            checker.local(2)

    def test_import_replays_and_resume_preserves_specialized_meaning(self):
        data, _, _ = split_rule()
        contract(PiecewiseVerifier(data))
        data = prune(data)
        # Use the saved source's endpoint language, not its much larger game.
        source = json.loads(Path(__file__).with_name('piecewise_axes_graph.state.json').read_text())
        source['shape_menu'] = data['shape_menu']
        search, game, config = import_graph(data, source)
        cert = search.certificate(game)
        self.assertTrue(PiecewiseVerifier(cert).audit()['open_nodes'])
        self.assertFalse(game.rejected(game.keys[game.roots[0]]))
        saved = json.loads(json.dumps(search.snapshot(game, config, fingerprint())))
        resumed, again, _ = restore(saved)
        self.assertEqual(PiecewiseVerifier(resumed.certificate(again)).proof_hash(), PiecewiseVerifier(cert).proof_hash())
        self.assertEqual(json.loads(json.dumps(game.snapshot())), json.loads(json.dumps(again.snapshot())))


if __name__ == '__main__':
    unittest.main()
