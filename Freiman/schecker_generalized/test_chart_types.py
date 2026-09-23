import copy
from fractions import Fraction as F
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from backward_gap_audit import BackwardAudit, inside, preimage
from chart_geometry import Domain, compare, relative_box
from chart_contact_example import verify_example
from cyclic_frontier_gaps import value
from explore import Q
from finite_type_game import Game
from search_chart_types import ChartSearch, engine_hash, restore_search
from test_frontier_repair import small_graph
from type_graph_geometry import Cell, decode, endpoint, full_labels, parameters, root_cells, swapped, transition
from verify_chart_types import ChartVerifier
from verify_cyclic_types import Verifier


class ChartGeometryTests(unittest.TestCase):
    def test_saved_contact_needs_the_correlation_and_replays_exactly(self):
        record = json.loads(Path(__file__).with_name('chart_contact_example.json').read_text())
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact contact replay')):
            self.assertIn('verified', verify_example(record)['status'])
            broken = copy.deepcopy(record)
            broken['first'], broken['second'] = broken['second'], broken['first']
            with self.assertRaises(ValueError):
                verify_example(broken)

    def test_game_snapshot_preserves_pending_repairs_and_negative_results(self):
        game = Game([('root',)], depth_first=False)
        def planner(key, rejected):
            if key == ('root',):
                target = ('second',) if rejected(('first',)) else ('first',)
                return [dict(key=target)], [target]
            return None
        game.run(planner, max_steps=1)
        game.reject(('first',), permanent=True)
        # The pending root retains its old dependency until it is replanned.
        saved = json.loads(json.dumps(game.snapshot()))
        restored = Game.restore(saved)
        self.assertEqual(restored.entries, game.entries)
        self.assertEqual(list(restored.queue), list(game.queue))
        self.assertEqual(restored.permanent_rejections, game.permanent_rejections)
        for g in (game, restored):
            g.run(planner, max_steps=3)
        self.assertEqual(json.loads(json.dumps(game.snapshot())), json.loads(json.dumps(restored.snapshot())))

    def test_chart_resume_is_identical_to_uninterrupted_discovery(self):
        here = Path(__file__).parent
        bank = json.loads((here/'adaptive_depth8_certificate.json').read_text())
        labels = [z for case in bank['cases'] for shape in case['types'] for z in shape]
        config = dict(chart_memory=1, states=6, bins=25, base=F(22, 25), balance=F(9, 10),
                      max_step=1, outer_depth=3, local_filter=False, reuse_pending=True,
                      adaptive_shapes=True, max_shapes=12)
        search = ChartSearch(labels, **config, shape_menu=[full_labels(1), full_labels(-1)])
        game = Game(search.roots(), depth_first=False)
        search.game = game
        game.run(search.planner, max_steps=5, seconds=60)
        fingerprint = engine_hash()
        state = json.loads(json.dumps(search.snapshot(game, config, fingerprint), default=str))
        resumed, replay = restore_search(state, fingerprint)
        with self.assertRaisesRegex(ValueError, 'engine changed'):
            restore_search(state, 'wrong hash')
        for s,g in ((search,game), (resumed,replay)):
            g.run(s.planner, max_steps=12, seconds=60)
        original_cert = json.loads(json.dumps(search.certificate(game)))
        restored_cert = json.loads(json.dumps(resumed.certificate(replay)))
        for field in ('cells', 'nodes', 'roots'):
            self.assertEqual(original_cert[field], restored_cert[field])
        self.assertEqual(json.loads(json.dumps(game.snapshot())), json.loads(json.dumps(replay.snapshot())))
        self.assertEqual(search.cells, resumed.cells)

        # A changed discovery engine may enlarge its candidate set. Recheck
        # positives and reopen every negative result before such a migration.
        game.reject(game.keys[-1], permanent=True)
        old = json.loads(json.dumps(search.snapshot(game, config, 'old engine'), default=str))
        upgraded, restored = restore_search(old, fingerprint, allow_upgrade=True)
        self.assertFalse(restored.permanent_rejections)
        self.assertFalse(any(e['status'] == 'rejected' for e in restored.entries))
        self.assertEqual(upgraded.state_upgrades[-1]['reopened'], 1)
        self.assertTrue(upgraded.state_upgrades[-1]['verified_local_rules'])
        broken = copy.deepcopy(old)
        e = next(e for e in broken['game']['entries'] if e['status'] == 'local')
        e['plan'][0]['suffixes'] = ['', '']
        with self.assertRaisesRegex(ValueError, 'upgrade audit'):
            restore_search(broken, fingerprint, allow_upgrade=True)

    def test_return_and_forward_routes_remain_available_together(self):
        search = ChartSearch([], chart_memory=1, max_step=1, outer_depth=0,
                             shape_menu=[full_labels(1), full_labels(-1)])
        routes = list(search.child_routes(1, '131213', '313121', search.cells[1].high))
        self.assertTrue(any(deps == [(1, False)] for _,deps in routes))
        self.assertTrue(any(deps != [(1, False)] for _,deps in routes))

    def test_backward_inverse_and_chart_images_match_direct_exact_parameters(self):
        base = parameters('32113', '4322')
        for words in (('1', ''), ('', '2'), ('1', '3'), ('131213', '313121')):
            for high in (False, True):
                direct = transition(base, *words, high)
                domain = Domain(base, words, high).validate()
                self.assertEqual(domain.outer, direct)
                self.assertEqual(relative_box(domain, domain), base)
                self.assertEqual(domain.exchange().outer, swapped(direct))
                for flip in (False, True):
                    result = swapped(direct) if flip else direct
                    point = tuple(b[0] for b in (result.r, result.s, result.ratio))
                    self.assertEqual(preimage(base, dict(suffixes=words, high=high), flip, point),
                                     tuple(b[0] for b in (base.r, base.s, base.ratio)))

    def test_comparisons_match_actual_point_geometry_for_both_directions(self):
        base = Cell(('', ''), 1, True, (Q(F(1, 2)),)*2, (Q(F(2, 3)),)*2, (Q(F(3, 5)),)*2)
        for words in (('1', ''), ('1', '1'), ('12', '3'), ('', '12')):
            for high in (False, True):
                domain = Domain(base, words, high).validate()
                actual = domain.outer
                points = [endpoint(domain.states, z) for z in
                          [('', a, '', b) for a in (False, True) for b in (False, True)]]
                params = tuple(b[0] for b in (actual.r, actual.s, actual.ratio))
                for a in points:
                    for b in points:
                        self.assertEqual(compare(domain, a, b), value(actual, params, a) >= value(actual, params, b))

    def test_common_words_cancel_before_bounding(self):
        base = Cell(('', ''), -1, True, (Q(F(1, 2)), Q(F(3, 4))),
                    (Q(F(1, 3)), Q(F(2, 5))), (Q(F(1, 2)), Q(F(3, 4))))
        source = Domain(base, ('12', '23'), False).validate()
        middle = transition(base, '1', '2', True)
        target = Domain(middle, ('2', '3'), False).validate()
        image = relative_box(source, target)
        self.assertEqual(image, middle)

    def test_every_saved_contracted_witness_is_excluded_without_decimals(self):
        here = Path(__file__).parent
        checker = Verifier(json.loads((here/'frontier_contracted_graph.json').read_text()))
        gaps = json.loads((here/'frontier_contracted_gaps.json').read_text())
        backward = BackwardAudit(checker)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact backward audit')):
            for w in gaps['witnesses']:
                self.assertEqual(backward.witness(w, 4)['status'], 'excluded')
        # A seed point must not be excluded, including at depth zero.
        root = root_cells()[0]
        point = tuple(x[0] for x in (root.r, root.s, root.ratio))
        self.assertEqual(backward.trace(checker.data['roots']['zero'], point, 0)['status'], 'reachable_from_n0')

    def test_chart_excludes_a_point_which_its_outer_box_contains(self):
        here = Path(__file__).parent
        checker = Verifier(json.loads((here/'frontier_contracted_graph.json').read_text()))
        witness = json.loads((here/'frontier_contracted_gaps.json').read_text())['witnesses'][0]
        point = tuple(map(decode, witness['parameters']))
        backward = BackwardAudit(checker)
        found = False
        for i, j, k in backward.incoming[witness['node']]:
            n = checker.nodes[i]
            edge = n['children'][j]
            domain = Domain(checker.cells[n['cell']], tuple(edge['suffixes']), edge['high'])
            if edge['destinations'][k]['swap']:
                domain = domain.exchange()
            if not inside(point, domain.outer):
                continue
            singleton = Cell(domain.states, domain.parity, domain.high, *((x, x) for x in point))
            pulled = relative_box(Domain(singleton, ('', ''), singleton.high), domain)
            self.assertTrue(pulled is None or not inside(tuple(x[0] for x in (pulled.r, pulled.s, pulled.ratio)), domain.base))
            found = True
        self.assertTrue(found)

    def test_empty_chart_preserves_the_old_exact_checker(self):
        data = small_graph()
        old = Verifier(data).audit()
        data['format'] = 'freiman-chart-types-v1'
        checker = ChartVerifier(data)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact chart audit')):
            new = checker.audit()
        self.assertFalse(new['failed_rules'])
        self.assertEqual(old['verified_rules'], new['verified_rules'])
        self.assertEqual(old['open_nodes'], new['open_nodes'])
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            checker.closed()

    def test_parameter_chart_union_rejects_an_interior_hole(self):
        base = Cell(('', ''), 1, True, (Q(F(1, 2)), Q(F(3, 4))),
                    (Q(F(1, 2)),)*2, (Q(F(1, 2)),)*2)
        source = Domain(base, ('', ''), True)
        def data_for(boxes):
            data = dict(format='freiman-chart-types-v1', cells=[], nodes=[], roots={})
            for rb in boxes:
                b = Cell(base.states, base.parity, base.high, rb, base.s, base.ratio)
                child = Domain(b, ('1', ''), False)
                lo, hi = full_labels(child.parity)
                data['cells'].append(child.record())
                data['nodes'].append(dict(cell=len(data['cells'])-1, lower=lo, upper=hi, children=[]))
            lo, hi = full_labels(-1)[::-1]
            edge = dict(suffixes=('1', ''), high=False, lower=lo, upper=hi,
                        destinations=[dict(node=i, swap=False) for i in range(len(boxes))])
            return ChartVerifier(data), edge
        checker, edge = data_for([(Q(F(1, 2)), Q(F(3, 5))), (Q(F(2, 3)), Q(F(3, 4)))])
        with self.assertRaisesRegex(ValueError, 'not covered'):
            checker.child(source, edge)
        checker, edge = data_for([(Q(F(1, 2)), Q(F(3, 5))), (Q(F(3, 5)), Q(F(3, 4)))])
        self.assertEqual(checker.child(source, edge)[2], [0, 1])
        edge['suffixes'] = ('', '')
        with self.assertRaisesRegex(ValueError, 'empty'):
            checker.child(source, edge)

    @unittest.skipUnless(shutil.which('c++'), 'C++17 compiler unavailable')
    def test_python_native_correlated_search_and_exact_replay(self):
        here = Path(__file__).parent
        bank = json.loads((here/'adaptive_depth8_certificate.json').read_text())
        labels = [z for case in bank['cases'] for shape in case['types'] for z in shape]
        results = []
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp)/'chart-planner'
            subprocess.run(['c++', '-O2', '-std=c++17', '-ffp-contract=off', '-DCORRELATED_CHARTS',
                            str(here/'cyclic_planner.cpp'), '-o', str(binary)], check=True)
            for native in (False, True):
                search = ChartSearch(labels, chart_memory=1, max_step=1, outer_depth=3, local_filter=False,
                         shape_menu=[full_labels(1), full_labels(-1)], adaptive_shapes=True, max_shapes=12)
                game = Game(search.roots(), depth_first=False)
                search.game = game
                if native:
                    search.native_executable = binary
                try:
                    game.run(search.planner, max_types=500, max_steps=8, seconds=60)
                finally:
                    search.close_native()
                cert = search.certificate(game)
                audit = ChartVerifier(cert).audit()
                self.assertFalse(audit['failed_rules'])
                self.assertTrue(audit['verified_rules'])
                self.assertTrue(audit['open_nodes'])
                results.append(cert)
        for key in ('cells', 'nodes', 'roots'):
            self.assertEqual(results[0][key], results[1][key])


if __name__ == '__main__':
    unittest.main()
