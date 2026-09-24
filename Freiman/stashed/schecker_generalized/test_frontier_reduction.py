import copy
import random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from contract_piecewise_charts import contract, prune
from explore import Q
from reduce_chart_frontier import cover_subsequence, dependencies, frontier_masks, trim
from test_piecewise_charts import split_rule
from verify_piecewise_charts import PiecewiseVerifier


class FrontierReductionTests(unittest.TestCase):
    def test_frontier_union_on_cycles_matches_independent_reachability(self):
        rng = random.Random(462)
        for _ in range(40):
            children = [set(rng.sample(range(12), rng.randrange(4))) for _ in range(12)]
            data = dict(nodes=[dict(cell=0, children=[dict(destinations=[dict(node=j) for j in sorted(ds)])]
                                     if ds else []) for ds in children])
            masks = frontier_masks(data)
            for start in range(12):
                seen, todo, expected = set(), [start], 0
                while todo:
                    i = todo.pop()
                    if i in seen:
                        continue
                    seen.add(i)
                    if not children[i]:
                        expected |= 1 << i
                    todo.extend(children[i])
                self.assertEqual(masks[start], expected)

    def solve_intervals(self, intervals, masks, beam=32):
        plan = [dict(lower=a, upper=b, suffixes=('1', ''), destinations=[dict(node=i)])
                for i, (a, b) in enumerate(intervals)]
        def ge(domain, a, b, strict=False):
            return a > b if strict else a >= b
        with patch('reduce_chart_frontier.endpoint', side_effect=lambda states, label, suffix: label), \
                patch('reduce_chart_frontier.compare', side_effect=ge):
            result = cover_subsequence(None, SimpleNamespace(states=('', '')), 0, 10, plan, masks, beam)
        return None if result is None else [plan.index(e) for e in result]

    def test_shared_unresolved_obligations_are_charged_once(self):
        self.assertEqual(self.solve_intervals([(0, 4), (0, 6), (3, 7), (6, 10)], [1, 6, 1, 1]), [0, 2, 3])

    def test_required_contact_cannot_be_removed_even_by_a_narrow_beam(self):
        self.assertEqual(self.solve_intervals([(0, 4), (4, 6), (6, 10)], [1, 1023, 1], 1), [0, 1, 2])
        self.assertIsNone(self.solve_intervals([(0, 4), (5, 10)], [1, 1]))

    def test_real_guarded_graph_retains_only_old_dependencies_and_stays_open(self):
        data, _, _ = split_rule()
        checker = PiecewiseVerifier(data)
        self.assertFalse(checker.audit()['failed_rules'])
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact frontier reduction')):
            contract(checker)
            before = dependencies(data)
            trim(checker)
            self.assertTrue(all(new <= old for old, new in zip(before, dependencies(data))))
            reduced = PiecewiseVerifier(prune(data))
            audit = reduced.audit()
        self.assertFalse(audit['failed_rules'])
        self.assertTrue(audit['open_nodes'])
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            reduced.closed()


if __name__ == '__main__':
    unittest.main()
