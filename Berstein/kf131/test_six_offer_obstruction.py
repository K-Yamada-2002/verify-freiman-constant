import copy
import unittest

from exact import hull
from type_certificates import endpoint
from six_offer_obstruction import (
    BASE, ENTRY, GAP_LABELS, UNIFORM_WITNESS, compute, verify, walk_tree,
)
from child_recurrence import PREFIXES


class SixOfferObstructionChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = compute()

    def test_uniform_certificate_and_every_initial_offer(self):
        result = verify(self.data)
        self.assertEqual(set(result['initial_exclusions']), {'A1', 'A2', 'B1', 'B2', 'D1'})
        self.assertEqual(result['relative_tree_nodes'], 66)
        self.assertEqual(result['checked_parameter_domains'], 5)

    def test_direct_actual_hulls_in_both_parities_and_late_returns(self):
        # An independent evaluation using actual words, without normalized
        # difference(), checks the orientation and suffix conventions.
        for n in (0, 1, 4, 9):
            u, v = (w+'2'*n for w in BASE)
            low, high = sorted(endpoint(u, v, e) for e in GAP_LABELS)
            leaf_endpoints = []
            for nodes, prefix in zip(self.data['relative_trees'], PREFIXES):
                for node in walk_tree(nodes, prefix):
                    a, b = hull(u+node['u'], v+node['v'])
                    self.assertTrue(b <= low or high <= a)
                    leaf_endpoints.extend((a, b))
            self.assertIn(low, leaf_endpoints)
            self.assertIn(high, leaf_endpoints)
            su, sv = (self.data['initial_witnesses'][n]
                      if n < ENTRY else UNIFORM_WITNESS)
            a, b = hull(u+su, v+sv)
            self.assertLess(low, a)
            self.assertLess(b, high)

    def test_omitted_legal_child_is_rejected(self):
        bad = copy.deepcopy(self.data)
        bad['relative_trees'][0][0]['children'].pop()
        with self.assertRaisesRegex(ValueError, 'incomplete or illegal split'):
            verify(bad)

    def test_wrong_leaf_side_is_rejected(self):
        bad = copy.deepcopy(self.data)
        node = next(n for n in bad['relative_trees'][0] if not n['children'])
        node['side'] = 'above' if node['side'] == 'below' else 'below'
        with self.assertRaisesRegex(ValueError, 'failed'):
            verify(bad)

    def test_wrong_witness_is_rejected_despite_saved_positive_bounds(self):
        bad = copy.deepcopy(self.data)
        bad['initial_witnesses'][0] = ['2', '2']
        with self.assertRaisesRegex(ValueError, 'witness.*failed'):
            verify(bad)


if __name__ == '__main__':
    unittest.main()
