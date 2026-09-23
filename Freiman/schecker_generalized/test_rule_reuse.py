import copy
import unittest
from unittest.mock import patch

from contract_piecewise_charts import edges
from explore import Q
from reduce_chart_frontier import frontier_masks
from reuse_chart_rules import install_recipe, reachable, reuse
from test_piecewise_charts import split_rule
from verify_piecewise_charts import PiecewiseVerifier


def clone_open_obligation():
    data, _, _ = split_rule()
    source = 2
    clone = copy.deepcopy(data['nodes'][source])
    clone['children'] = []
    index = len(data['nodes'])
    data['nodes'].append(clone)
    for node in data['nodes']:
        for edge in edges(node):
            old = next((d for d in edge['destinations'] if d['node'] == source), None)
            if old is not None:
                edge['destinations'].append(dict(node=index, swap=old['swap']))
                return data, source, index
    raise AssertionError('fixture source has no incoming edge')


def redundant_destination():
    data, _, _ = split_rule()
    index = 2
    recipe = copy.deepcopy(data['nodes'][index]['children'])
    edge = data['nodes'][index]['children'][0]
    old = edge['destinations'][0]
    clone = copy.deepcopy(data['nodes'][old['node']])
    clone.pop('pieces', None)
    clone['children'] = []
    edge['destinations'].append(dict(node=len(data['nodes']), swap=old['swap']))
    data['nodes'].append(clone)
    return data, index, recipe


class RuleReuseTests(unittest.TestCase):
    def test_existing_recipe_is_replayed_on_an_open_type_without_new_nodes(self):
        data, source, index = clone_open_obligation()
        checker = PiecewiseVerifier(data)
        self.assertFalse(checker.audit()['failed_rules'])
        active = reachable(data)
        masks = frontier_masks(data)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact recipe replay')):
            ok, error = install_recipe(checker, index, data['nodes'][source]['children'], masks)
            self.assertTrue(ok, error)
            checker.local(index)
        self.assertEqual(reachable(data), active)
        self.assertFalse(checker.audit()['failed_rules'])
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            checker.closed()

    def test_illegal_empty_step_recipe_is_rejected_and_restored(self):
        data, source, index = clone_open_obligation()
        checker = PiecewiseVerifier(data)
        node = data['nodes'][index]
        invalid = [dict(suffixes=['', ''], high=checker.cells[node['cell']].high,
                        lower=node['lower'], upper=node['upper'], destinations=[dict(node=source, swap=False)])]
        ok, error = install_recipe(checker, index, invalid, frontier_masks(data))
        self.assertFalse(ok)
        self.assertIn('empty', error)
        self.assertEqual(node['children'], [])
        self.assertNotIn(index, checker.checked)

    def test_portfolio_reuse_preserves_reachability_and_unresolved_accounting(self):
        data, _, index = clone_open_obligation()
        checker = PiecewiseVerifier(data)
        checker.audit()
        before = reachable(data)
        result = reuse(checker, seconds=10, candidates=32)
        self.assertGreaterEqual(result['statistics']['accepted'], 1)
        self.assertTrue(data['nodes'][index]['children'])
        self.assertEqual(reachable(data), before)
        self.assertFalse(checker.audit()['failed_rules'])

    def test_local_recipe_replacement_removes_a_real_open_dependency(self):
        data, index, recipe = redundant_destination()
        checker = PiecewiseVerifier(data)
        self.assertFalse(checker.audit()['failed_rules'])
        roots = copy.deepcopy(data['roots'])
        active = reachable(data)
        masks = frontier_masks(data)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in exact strategy change')):
            ok, error = install_recipe(checker, index, recipe, masks, replace_local=True)
            self.assertTrue(ok, error)
            self.assertFalse(checker.audit()['failed_rules'])
        self.assertLess(bin(frontier_masks(data)[index]).count('1'), bin(masks[index]).count('1'))
        self.assertLess(reachable(data), active)
        self.assertEqual(roots, data['roots'])

    def test_failed_local_replacement_restores_parameter_pieces(self):
        data, index, _ = redundant_destination()
        node = data['nodes'][index]
        destination = node['children'][0]['destinations'][0]['node']
        node['pieces'] = [dict(cell=node['cell'], children=node['children'])]
        node['children'] = []
        old = copy.deepcopy(node)
        checker = PiecewiseVerifier(data)
        self.assertFalse(checker.audit()['failed_rules'])
        invalid = [dict(suffixes=['', ''], high=checker.cells[node['cell']].high,
                        lower=node['lower'], upper=node['upper'],
                        destinations=[dict(node=destination, swap=False)])]
        ok, error = install_recipe(checker, index, invalid, frontier_masks(data), replace_local=True)
        self.assertFalse(ok)
        self.assertIn('empty', error)
        self.assertEqual(node, old)
        self.assertFalse(checker.audit()['failed_rules'])


if __name__ == '__main__':
    unittest.main()
