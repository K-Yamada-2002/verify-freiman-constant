"""Cross-check the finite-scale calculation against independent exact arithmetic."""
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest

from exact import cylinder
from numerical_points import certify, search


class NumericalPointChecks(unittest.TestCase):
    def test_search_has_rationally_certified_periodic_witnesses(self):
        with localcontext() as context:
            context.prec = 90
            for text in ['1.29288', '1.292906', '1.2928873425']:
                u, v, _ = search(Decimal(text), Decimal('1e-40'), Decimal(10).sqrt(), 10000)
                self.assertIsNotNone(u)
                self.assertLess(certify(Fraction(text),u,v,Fraction(1,10**40)), Fraction(1,10**40))


@unittest.skipUnless(shutil.which('c++'), 'C++ compiler unavailable')
class NumericalCoverChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.binary = str(Path(cls.temporary.name)/'cover')
        subprocess.run(['c++','-O2','-std=c++17',str(Path(__file__).with_name('numerical_cover.cpp')),
                        '-o',cls.binary], check=True, capture_output=True)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_integer_bounds_against_q_sqrt10_and_decimal(self):
        words = [''.join(w) for n in range(6) for w in product('123', repeat=n)
                 if '131' not in ''.join(w)]
        rng = random.Random(123)
        while len(words)<500:
            word = ''.join(rng.choice('123') for _ in range(12))
            if '131' not in word:
                words.append(word)
        data=json.loads(subprocess.check_output([self.binary,'--cylinders',*words], text=True))
        scale=10**15
        for row in data:
            lo, hi = cylinder(row['word'])
            a,b,c,d = [Fraction(z,scale) for z in row['bounds']]
            self.assertLessEqual(a,lo)
            self.assertLessEqual(lo,b)
            self.assertLessEqual(c,hi)
            self.assertLessEqual(hi,d)
            self.assertLessEqual(d-a-(hi-lo),Fraction(2,scale))
            with localcontext() as context:
                context.prec = 90
                # Compare the independently written Decimal discovery as well.
                from numerical_points import prefix
                z=prefix(row['word'],Decimal(10).sqrt())
                self.assertLessEqual(abs(z.lo-Decimal(lo.decimal(80))),Decimal('1e-79'))
                self.assertLessEqual(abs(z.hi-Decimal(hi.decimal(80))),Decimal('1e-79'))

    def test_exhaustive_counts_match_existing_exact_run(self):
        data=json.loads(subprocess.check_output([self.binary,'7','200000000','--no-prune'],text=True))
        self.assertEqual(data['visited'],69613)
        self.assertEqual(data['accepted_sum_hulls'],45254)
        self.assertTrue(data['covers_target_at_this_finite_scale_only'])
        pruned=json.loads(subprocess.check_output([self.binary,'7'],text=True))
        self.assertTrue(pruned['covers_target_at_this_finite_scale_only'])
        self.assertEqual(pruned['covered_grid_units'],26000000000)
        self.assertGreater(pruned['redundant_subtrees'],0)

    def test_budget_does_not_masquerade_as_success(self):
        data=json.loads(subprocess.check_output([self.binary,'12','10'],text=True))
        self.assertTrue(data['budget_exhausted'])
        self.assertFalse(data['covers_target_at_this_finite_scale_only'])


if __name__ == '__main__':
    unittest.main()
