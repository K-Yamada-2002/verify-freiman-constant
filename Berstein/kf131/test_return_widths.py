import unittest

from exact import F
from anchored_geometry import B,factor
from scalar_geometry import uniform_child_core
from audit_return_widths import margins,expansion_witness


class ReturnWidthTests(unittest.TestCase):
    def test_expansion_witness_does_not_confuse_a_contraction_with_growth(self):
        self.assertIsNone(expansion_witness([{0:B(F(1,2))}]))
        self.assertIsNotNone(expansion_witness([{1:B(2)},{0:B(1)}]))

    def test_weighted_contraction_can_have_a_row_sum_above_one(self):
        self.assertIsNotNone(margins([{1:B(2)},{0:B(F(1,8))}],[F(3),F(1)]))
        self.assertIsNone(margins([{1:B(2)},{0:B(F(1,2))}],[F(2),F(1)]))

    def test_affine_width_matches_independent_endpoint_formula(self):
        r,s,h = F(2,5),F(3,5),F(2,3)
        for u,v in [('3',''),('','1'),('2','2'),('2233','3311')]:
            fu,fv = factor(u,r),factor(v,s)
            swap = h*(fu/fv)**2 > 1
            a,b = uniform_child_core(u,v,swap,(F(0),F(1)),(r,r),(s,s),(h,h),-1)
            self.assertEqual(b-a,h/fv**2 if swap else 1/fu**2)


if __name__ == '__main__':
    unittest.main()
