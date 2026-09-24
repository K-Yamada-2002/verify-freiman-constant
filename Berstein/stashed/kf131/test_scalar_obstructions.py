import copy
import json
from pathlib import Path
import unittest

from exact import F, Q
from anchored_geometry import B
from scalar_obstructions import discover, physical_obstruction, replay, uniform_gap


class ScalarObstructionsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = json.loads(Path(__file__).with_name('scalar_obstructions_20260924.json').read_text())['obstructions']

    def test_all_exact_witnesses(self):
        self.assertEqual(len(self.rows),8)
        for row in self.rows:
            self.assertGreater(replay(row)['leaves'],0)

    def test_uniform_and_physical_gaps(self):
        count = 0
        for row in self.rows:
            self.assertEqual(uniform_gap(row),row['uniform_gap'])
            if 'physical_prefixes' in row:
                count += 1
                self.assertEqual(physical_obstruction(row),row['physical_verification'])
                def decode(x):
                    return B(Q(F(x['a']['a']),F(x['a']['b'])),
                             Q(F(x['b']['a']),F(x['b']['b'])))
                a,b = map(F,row['physical_scalar_gap'])
                self.assertTrue(decode(row['uniform_gap'][0]) < a < b < decode(row['uniform_gap'][1]))
        self.assertEqual(count,2)

    def test_missing_branch_rejected(self):
        row = copy.deepcopy(self.rows[0])
        row['tree'][0]['children'].pop()
        with self.assertRaisesRegex(ValueError,'incomplete legal split'):
            replay(row)

    def test_wrong_parameter_rejected(self):
        row = copy.deepcopy(self.rows[0])
        row['parameters'][2] = '2'
        with self.assertRaisesRegex(ValueError,'outside parameter box'):
            replay(row)

    def test_fake_leaf_rejected(self):
        row = copy.deepcopy(self.rows[0])
        row['tree'] = [dict(u='',v='',children=[])]
        with self.assertRaisesRegex(ValueError,'does not exclude'):
            replay(row)

    def test_budget_exhaustion_not_exclusion(self):
        # alpha is allowed on both sides, so t=0 is a genuine sum value.
        self.assertIsNone(discover(('',''),1,(F(2,5),F(2,5),F(1)),F(0),budget=20))

    def test_wrong_physical_prefix_rejected(self):
        row = copy.deepcopy(next(r for r in self.rows if 'physical_prefixes' in r))
        row['physical_prefixes'] = ['2','2']
        with self.assertRaises(ValueError):
            physical_obstruction(row)


if __name__ == '__main__':
    unittest.main()
