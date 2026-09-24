import copy
import json
from itertools import product
from fractions import Fraction as F
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from explore import Q, matrix, state_of
from finite_type_game import Game
from type_graph_geometry import (Cell, anchor, delta_range, endpoint, full_labels,
                                 parameters, root_cells, square, transition)
from verify_cyclic_types import Verifier, contains_box, cover_parameter_box
from search_cyclic_types import Search
import run_cyclic_search


class FiniteGameTests(unittest.TestCase):
    def test_repair_to_closed_cycle(self):
        choices = {0: [(1,), (2,)], 1: [], 2: [(2,)]}

        def plan(key, rejected):
            return next(((c, c) for c in choices[key] if not any(map(rejected, c))), None)

        game = Game([0]).run(plan, max_types=20)
        self.assertTrue(game.closed())
        self.assertEqual({game.keys[i] for i in game.reachable()}, {0, 2})
        self.assertGreater(game.repairs, 0)
        self.assertNotIn(game.ids[0], game.entries[game.ids[1]]['parents'])

    def test_resource_limit_keeps_open_obligations(self):
        game = Game([0]).run(lambda key, _: (None, [key+1]), max_types=4)
        self.assertFalse(game.closed())
        self.assertEqual(game.stop, 'type limit')
        self.assertEqual(game.summary()['rejected'], 0)
        self.assertGreater(game.summary()['unresolved'], 0)

    def test_matches_independent_greatest_fixed_point(self):
        rng = random.Random(462)
        for _ in range(100):
            size = rng.randrange(1, 15)
            options = [[tuple(rng.sample(range(size), rng.randrange(1, min(4, size)+1)))
                        for _ in range(rng.randrange(4))] for _ in range(size)]
            alive = set(range(size))
            while True:
                new = {i for i in alive if any(set(plan) <= alive for plan in options[i])}
                if new == alive:
                    break
                alive = new

            def plan(key, rejected):
                return next(((c, c) for c in options[key] if not any(map(rejected, c))), None)

            for dfs in (False, True):
                game = Game([0], depth_first=dfs).run(plan, max_types=100, max_steps=10000)
                self.assertEqual(game.closed(), 0 in alive)
                self.assertEqual(game.ids[0] in game.supported(), game.closed())


class ExactGeometryTests(unittest.TestCase):
    def test_periodic_return_and_entire_initial_family(self):
        zero, positive = root_cells()
        for cell in (zero, positive):
            image = transition(cell, '131213', '313121', True)
            self.assertEqual(image.ratio, zero.ratio)
            self.assertTrue(contains_box(positive.r, image.r))
            self.assertTrue(contains_box(positive.s, image.s))
        self.assertEqual(matrix('313121'), (14, 19, 53, 72))
        for n in range(1, 20):
            actual = parameters('3211'+'313121'*n+'3', '4322'+'313121'*n)
            self.assertEqual(actual.ratio, positive.ratio)
            self.assertTrue(contains_box(positive.r, actual.r))
            self.assertTrue(contains_box(positive.s, actual.s))

    def test_transition_against_independent_prefix_matrices(self):
        for u, v in (('32113', '4322'), ('321132', '432213'), ('231', '132')):
            for du, dv in (('1', ''), ('', '32'), ('21', '3')):
                for oldh in (False, True):
                    for newh in (False, True):
                        cell = parameters(u, v, oldh)
                        image = transition(cell, du, dv, newh)
                        actual = parameters(u+du, v+dv, newh)
                        self.assertEqual(image, actual)

    def test_delta_bounds_and_interior_critical_point(self):
        # General nonextremal alpha exercises the critical-point branch.
        cases = [(Q(F(1, 2)), Q(F(1, 4)), Q(F(4, 5)))]
        for high in (False, True):
            cases.append((anchor('3', high), anchor('3', False), anchor('3', True)))
        for a, x, y in cases:
            box = (Q(F(1, 4)), Q(1))
            lo, hi = delta_range(a, x, y, box)
            for j in range(21):
                r = box[0]+(box[1]-box[0])*F(j, 20)
                actual = (x-y)*square(1+a*r)/((1+x*r)*(1+y*r))
                self.assertLessEqual(lo, actual)
                self.assertLessEqual(actual, hi)

    def test_endpoint_legality_and_interpolation(self):
        a = endpoint(('3', ''), ('1@1/2', False, '', False))
        self.assertGreater(a[0], 0)
        for label in [('1313', False, '', False), ('4', False, '', False),
                      ('@3/2', False, '', False)]:
            with self.assertRaises(ValueError):
                endpoint(('3', ''), label)


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Real Freiman geometry, kept small. Leaves are deliberately open.
        labels = [('', a, '', b) for a in (False, True) for b in (False, True)]
        cls.search = Search(labels, bins=12, base=F(4, 5), max_step=2, variants=2)
        game = Game(cls.search.roots()).run(cls.search.planner, max_types=100, max_steps=3, seconds=30)
        cls.data = cls.search.certificate(game)

    def test_local_audit_uses_no_decimal_arithmetic(self):
        with patch.object(Q, 'decimal', side_effect=AssertionError('floating verifier')):
            result = Verifier(self.data).audit()
        self.assertGreater(len(result['verified_rules']), 0)
        self.assertEqual(result['failed_rules'], [])
        self.assertGreater(len(result['open_nodes']), 0)

    def test_success_flag_does_not_hide_open_leaf(self):
        data = copy.deepcopy(self.data)
        data['search']['closed_candidate'] = True
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            Verifier(data).closed()

    def test_missing_root_case_rejected(self):
        data = copy.deepcopy(self.data)
        del data['roots']['positive']
        with self.assertRaisesRegex(ValueError, 'both n=0'):
            Verifier(data).closed()

    def test_empty_successor_and_missing_ratio_coverage_rejected(self):
        for mutation, message in (('empty', 'empty or illegal'), ('destinations', 'missing parameter')):
            data = copy.deepcopy(self.data)
            i = next(i for i, node in enumerate(data['nodes']) if node['children'])
            edge = data['nodes'][i]['children'][0]
            if mutation == 'empty':
                edge['suffixes'] = ['', '']
            else:
                edge['destinations'] = []
            with self.assertRaisesRegex(ValueError, message):
                Verifier(data).local(i)

    def test_ratio_contact_and_gap(self):
        Verifier.cover_ratio((Q(1), Q(3)), [(Q(1), Q(2)), (Q(2), Q(3))])
        with self.assertRaisesRegex(ValueError, 'gap'):
            Verifier.cover_ratio((Q(1), Q(3)), [(Q(1), Q(F(3, 2))), (Q(2), Q(3))])

    def test_three_dimensional_coverage_and_hidden_hole(self):
        image = ((Q(0), Q(1)),)*3
        halves = ((Q(0), Q(F(1, 2))), (Q(F(1, 2)), Q(1)))
        cover_parameter_box(image, list(product(halves, repeat=3)))
        # All eight corners are covered, but most of the cube is missing.
        corners = ((Q(0), Q(F(1, 4))), (Q(F(3, 4)), Q(1)))
        with self.assertRaisesRegex(ValueError, 'gap'):
            cover_parameter_box(image, list(product(corners, repeat=3)))
        cover_parameter_box(((Q(F(1, 2)),)*2,)*3, list(product(halves, repeat=3)))

    def test_split_actual_child_domain_preserves_local_rule(self):
        from type_graph_geometry import transition, swapped
        data = copy.deepcopy(self.data)
        checker = Verifier(data)
        i = next(i for i, n in enumerate(data['nodes']) if n['children'])
        edge = data['nodes'][i]['children'][0]
        parent = checker.cells[data['nodes'][i]['cell']]
        image = transition(parent, *edge['suffixes'], edge['high'])
        dest = edge['destinations'][0]
        if dest['swap']:
            image = swapped(image)
        node = data['nodes'][dest['node']]
        cell = checker.cells[node['cell']]
        cut = sum(image.r)/2
        self.assertLess(cell.r[0], cut)
        self.assertLess(cut, cell.r[1])
        replacements = []
        for interval in ((cell.r[0], cut), (cut, cell.r[1])):
            child = Cell(cell.states, cell.parity, cell.high, interval, cell.s, cell.ratio)
            new_node = copy.deepcopy(node)
            new_node['cell'] = len(data['cells'])
            data['cells'].append(child.record())
            replacements.append(dict(node=len(data['nodes']), swap=dest['swap']))
            data['nodes'].append(new_node)
        edge['destinations'][:1] = replacements
        Verifier(data).local(i)

    def test_adaptive_boxes_form_complete_exact_partition(self):
        search = Search([('', False, '', False)], bins=3, outer_depth=0, local_filter=False)
        cid = 2
        search.blocked_cells[cid] = 10
        changed = search.refine_boxes(1)
        self.assertEqual(len(changed), 1)
        parent = search.cells[cid]
        kids = [search.cells[i] for i in search.active_leaves(cid)]
        cover_parameter_box((parent.r, parent.s, parent.ratio),
                            [(c.r, c.s, c.ratio) for c in kids])
        self.assertTrue(all(c != parent for c in kids))

    def test_reuse_containing_current_type(self):
        search = Search([('@1/2', False, '', False)], bins=3, outer_depth=0, local_filter=False)
        game = Game(search.roots())
        search.game = game
        current = search.roots()[1]
        mid = next(i for i, row in enumerate(search.points(1)) if '@' in row[1][0])
        self.assertEqual(search.reuse_target((1, current[1], mid), current), current)

    def test_pending_reuse_retains_the_unresolved_obligation(self):
        search = Search([('@1/2', False, '', False)], bins=3, outer_depth=0,
                        local_filter=False, reuse_pending=True)
        game = Game(search.roots())
        search.game = game
        current, waiting = search.roots()
        mid = next(i for i, row in enumerate(search.points(1)) if '@' in row[1][0])
        offered = (1, waiting[1], mid)
        self.assertEqual(search.reuse_target(offered, current), waiting)
        self.assertEqual(search.target_cost(waiting, current), 1)
        self.assertEqual(search.target_cost(offered, current), 2)
        self.assertFalse(game.closed())
        self.assertEqual(game.summary()['unresolved'], 2)
        with self.assertRaisesRegex(ValueError, 'unresolved type'):
            Verifier(search.certificate(game)).closed()

    def test_periodic_boundary_does_not_add_adjacent_bin(self):
        search = Search([], bins=6, outer_depth=0, local_filter=False)
        cid = next(i for i, cell in enumerate(search.cells) if i >= 2 and
                   cell.states == ('3', '1') and cell.parity == -1 and cell.high
                   and cell.ratio[1] == Q(F(22, 25)**2))
        image = search.image(cid, '131213', '313121', True)
        self.assertEqual(search.destinations(image), [(cid, False)])
        cell = search.cells[cid]
        actual = transition(cell, '131213', '313121', True)
        cover_parameter_box((actual.r, actual.s, actual.ratio),
                            [(cell.r, cell.s, cell.ratio)])

    def test_lazy_memory_domains_contain_actual_parameters(self):
        search = Search([], bins=160, base=F(49, 50), memory=3,
                        outer_depth=0, local_filter=False)
        for u, v in (('32113', '4322'), ('212313', '332121'), ('113131', '222132')):
            cell = parameters(u, v)
            r, s = float(cell.r[0].a), float(cell.s[0].a)
            ids = search.generic_candidates(cell.states, cell.parity, cell.high,
                                             (r, r), (s, s), (.5, .5))
            self.assertTrue(ids)
            self.assertTrue(all(contains_box(search.cells[j].r, cell.r) and
                                contains_box(search.cells[j].s, cell.s) for j in ids))
        self.assertLess(len(search.cells), 30)

    def test_failure_pruning_is_optional_and_cleared_on_refinement(self):
        search = Search([('@1/2', False, '', False)], bins=3, outer_depth=0,
                        local_filter=False, prune_supersets=True)
        outer = search.roots()[1]
        mid = next(i for i, row in enumerate(search.points(1)) if '@' in row[1][0])
        inner = (1, outer[1], mid)
        search.remember_failure(inner)
        self.assertTrue(search.avoid_type(outer))
        search.prune_supersets = False
        self.assertFalse(search.avoid_type(outer))
        search.blocked_cells[2] = 10
        search.refine_boxes(1)
        self.assertFalse(search.failed_intervals)

    def test_endpoint_growth_rebuilds_the_dependent_tables(self):
        search = Search([], bins=6, max_step=1, outer_depth=1, local_filter=False)
        before = len(search.points(1))
        search.moves(1)
        result = search.grow_endpoint_menu(8)
        self.assertGreater(result['added_labels'], 0)
        self.assertGreater(len(search.points(1)), before)
        self.assertEqual(search.moves.cache_info().currsize, 0)
        for cid, lo, hi in search.roots():
            expected = tuple(endpoint(search.cells[cid].states, z)
                             for z in full_labels(search.cells[cid].parity))
            self.assertEqual((search.points(cid)[lo][2], search.points(cid)[hi][2]), expected)

    def test_direct_returns_are_not_cut_off_by_farthest_endpoint_limit(self):
        # Discovery-only fixture: two known short intervals cover the parent,
        # but the sole farthest endpoint proposes a fresh, larger obligation.
        pool = tuple(((i/12, 0.), (str(i), False, '', False), (i, 0)) for i in range(13))
        move = ('1', '', False, [(1, False)], [tuple(range(13))],
                [p[0] for p in pool], pool, list(range(13)), [()] * 13)
        outcomes = []
        for enabled in (False, True):
            search = Search([], bins=1, variants=1, outer_depth=0, local_filter=False,
                            return_offers=enabled)
            search.points = lambda _: pool
            search.moves = lambda _: [move]
            root = (0, 0, 10)
            game = Game([root])
            search.game = game
            known = [(1, 0, 5), (1, 5, 10)]
            for key in known:
                game.entries[game.add(key)]['status'] = 'local'
            result = search.planner(root, game.rejected)
            self.assertIsNotNone(result)
            outcomes.append(result[1])
        self.assertEqual(outcomes[0], [(1, 0, 12)])
        self.assertEqual(outcomes[1], known)

    def test_runner_rechecks_forged_success(self):
        data = copy.deepcopy(self.data)
        data['search']['closed_candidate'] = True

        def fake_run(command, **kwargs):
            output = Path(command[command.index('--output')+1])
            output.write_text(json.dumps(data))
            return SimpleNamespace(returncode=0)

        with tempfile.TemporaryDirectory() as tmp:
            plan = Path(tmp)/'plan.json'
            plan.write_text('[{}]')
            with patch('sys.argv', ['runner', '--plan', str(plan), '--output-dir', tmp]), \
                    patch.object(run_cyclic_search.subprocess, 'run', side_effect=fake_run), \
                    patch('builtins.print'):
                run_cyclic_search.main()
            report = json.loads((Path(tmp)/'summary.json').read_text())
        self.assertFalse(report['stages'][0]['accepted'])
        self.assertGreater(report['stages'][0]['audit']['unresolved'], 0)

    def test_runner_timeout_does_not_load_previous_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            plan = Path(tmp)/'plan.json'
            plan.write_text('[{}]')
            (Path(tmp)/'stage-1.json').write_text(json.dumps(self.data))
            with patch('sys.argv', ['runner', '--plan', str(plan), '--output-dir', tmp]), \
                    patch.object(run_cyclic_search.subprocess, 'run',
                                 side_effect=subprocess.TimeoutExpired('test', 1)), \
                    patch('builtins.print'):
                run_cyclic_search.main()
            report = json.loads((Path(tmp)/'summary.json').read_text())
        self.assertFalse(report['stages'][0]['accepted'])
        self.assertTrue(report['stages'][0]['hard_timeout'])
        self.assertNotIn('search', report['stages'][0])


class NativePlannerTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('c++'), 'C++17 compiler unavailable')
    def test_persistent_native_matches_python_and_exact_audit(self):
        directory = Path(__file__).resolve().parent
        data = json.loads((directory/'adaptive_depth8_certificate.json').read_text())
        labels = [z for case in data['cases'] for shape in case['types'] for z in shape]
        with tempfile.TemporaryDirectory() as tmp:
            binary = Path(tmp)/'planner'
            subprocess.run(['c++', '-O2', '-std=c++17', '-ffp-contract=off',
                            str(directory/'cyclic_planner.cpp'), '-o', str(binary)], check=True)
            for pending in (False, True):
                results = []
                for native in (False, True):
                    search = Search(labels, max_step=2, outer_depth=3, local_filter=False,
                                    reuse_pending=pending)
                    game = Game(search.roots())
                    search.game = game
                    if native:
                        search.native_executable = binary
                    try:
                        game.run(search.planner, max_types=500, max_steps=8, seconds=60)
                    finally:
                        search.close_native()
                    cert = search.certificate(game)
                    results.append(cert)
                    self.assertFalse(Verifier(cert).audit()['failed_rules'])
                for key in ('cells', 'nodes', 'roots'):
                    self.assertEqual(results[0][key], results[1][key])


if __name__ == '__main__':
    unittest.main()
