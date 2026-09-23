import copy
import json
from pathlib import Path
import unittest

from verify_type_graph import Verifier


HERE = Path(__file__).resolve().parent


class TypeGraphChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((HERE/'adaptive_type_graph.json').read_text())

    def test_root_and_all_six_immediate_arrival_types(self):
        verifier = Verifier(self.data)
        self.assertEqual(verifier.local(0)['dependencies'], list(range(1, 7)))
        for j in range(1, 7):
            self.assertTrue(verifier.local(j)['dependencies'])
        self.assertEqual(len(verifier.seed()), 2)

    def test_saved_audit_matches_the_graph(self):
        audit = json.loads((HERE/'adaptive_type_graph_audit.json').read_text())
        self.assertEqual(audit['proof_hash'], Verifier(self.data).proof_hash())
        self.assertEqual(len(audit['verified_rules']), 1676)
        self.assertEqual(len(audit['open_nodes']), 698)
        self.assertEqual(audit['failed_rules'], [])

    def test_cached_root_does_not_hide_open_children(self):
        data = copy.deepcopy(self.data)
        data['nodes'] = data['nodes'][:7]
        for node in data['nodes'][1:]:
            node['covered'] = False
            node['children'] = []
        verifier = Verifier(data)
        verifier.local(0)
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            verifier.closed()

    def test_missing_parameter_image_piece_is_rejected(self):
        data = copy.deepcopy(self.data)
        data['nodes'][0]['children'][0]['destinations'].pop()
        with self.assertRaisesRegex(ValueError, 'destination parameter boxes|do not cover the image'):
            Verifier(data).local(0)

    def test_wrong_arrival_parity_is_rejected(self):
        data = copy.deepcopy(self.data)
        data['nodes'][1]['parity'] *= -1
        with self.assertRaisesRegex(ValueError, 'arrival parity'):
            Verifier(data).local(0)

    def test_uncovered_parent_end_is_rejected(self):
        data = copy.deepcopy(self.data)
        data['nodes'][0]['children'].pop()
        with self.assertRaisesRegex(ValueError, 'upper end not covered'):
            Verifier(data).local(0)

    def test_trimming_parent_does_not_require_first_child_to_reach_its_start(self):
        data = copy.deepcopy(self.data)
        last = data['nodes'][0]['children'][-1]
        u, v = last['suffixes']
        a, h, b, k = last['lower']
        data['nodes'][0]['lower'] = [u+a, h, v+b, k]
        verifier = Verifier(data)
        first_upper = verifier.child(0, data['nodes'][0]['children'][0])[0][1]
        self.assertFalse(verifier.ge(0, first_upper, verifier.points(0)[0], strict=True))
        self.assertTrue(verifier.local(0)['dependencies'])

    def test_seed_can_mix_extremal_and_periodic_endpoint_fields(self):
        data = copy.deepcopy(self.data)
        data['nodes'][0]['lower'][2] = '~2'
        values = Verifier(data).seed()
        self.assertEqual(len(values), 2)
        self.assertIsInstance(values[0]['a'], dict)


if __name__ == '__main__':
    unittest.main()
