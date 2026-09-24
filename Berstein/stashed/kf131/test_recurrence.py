import json
from pathlib import Path
import unittest
from exact import F
from type_certificates import verify, endpoint, node_interval
from uniform_cover import compute, ROOT, CHILDREN


class RecurrenceChecks(unittest.TestCase):
    def test_uniform_cover_and_actual_initial_targets(self):
        result = compute()
        self.assertEqual(len(result['checks']), 8)
        lo, hi = [endpoint('112', '122', e) for e in ROOT]
        self.assertLess(lo, F('1.29288'))
        self.assertLess(F('1.292906'), hi)
        blo, bhi = [endpoint('112', '122', e) for e in CHILDREN[1]]
        clo, _ = [endpoint('112', '122', e) for e in CHILDREN[2]]
        self.assertLess(blo, F('1.2924533'))
        self.assertLess(F('1.2924537'), bhi)
        self.assertLess(F('1.2924537'), clo)

    def test_saved_exact_certificate_with_gap_constraint(self):
        path = Path(__file__).with_name('type_certificate_gap_d8.json')
        data = json.loads(path.read_text())
        self.assertEqual(verify(data), data['verification'])
        self.assertTrue(any(
            node_interval(data['nodes'][i])[0] <= F('1.29288')
            and F('1.292906') <= node_interval(data['nodes'][i])[1]
            for i in data['roots']))

    def test_broken_successor_cover_rejected(self):
        path = Path(__file__).with_name('type_certificate_gap_d8.json')
        data = json.loads(path.read_text())
        data['nodes'][data['roots'][2]]['children'] = []
        with self.assertRaises(AssertionError):
            verify(data)


if __name__ == '__main__':
    unittest.main()
