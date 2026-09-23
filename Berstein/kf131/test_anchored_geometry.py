import unittest

from exact import F, Q, matrix, transform
from anchored_geometry import (
    ALPHA, B, delta_range, difference_range, factor, parameters,
    position, transition,
    tail_endpoint,
)


class AnchoredGeometryChecks(unittest.TestCase):
    def test_biquadratic_arithmetic_and_exact_order(self):
        sqrt2, sqrt10 = B(0, 1), B(Q(0, 1))
        self.assertEqual(sqrt2**2, 2)
        self.assertEqual(sqrt10**2, 10)
        self.assertEqual((sqrt2*sqrt10)**2, 20)
        self.assertLess(sqrt2, F(3, 2))
        self.assertLess(F(7, 5), sqrt2)
        self.assertLess(sqrt10-2*sqrt2, F(1, 2))
        for x in (ALPHA, sqrt10-sqrt2, 3-sqrt2-sqrt10):
            self.assertEqual(x/x, 1)
            self.assertEqual(x*(1/x), 1)
            self.assertEqual((-x).sign(), -x.sign())

    def test_exact_half_ratio_and_common_two_identity(self):
        self.assertEqual(parameters('112', '122')[2], F(1, 2))
        for r in (F(1, 4), F(2, 5), F(4, 5)):
            self.assertEqual(factor('2', r), 2+ALPHA)
        image = transition('2', '2', (F(1, 4), F(4, 5)),
                           (F(1, 4), F(4, 5)), (F(49, 100), F(51, 100)), 1)
        self.assertEqual(image[2], (B(F(49, 100)), B(F(51, 100))))
        self.assertEqual(image[3], 1)

    def test_updates_against_actual_continued_fraction_matrices(self):
        for u, v in (('112', '122'), ('11212', '1222'), ('1122', '1223')):
            r, s, h, parity = parameters(u, v)
            for a, b in (('2', '2'), ('12', '3'), ('', '11'), ('3', '')):
                actual = parameters(u+a, v+b)
                image = transition(a, b, (r, r), (s, s), (h, h), parity)
                self.assertEqual(image, ((B(actual[0]),)*2, (B(actual[1]),)*2,
                                         (actual[2],)*2, actual[3]))

    def test_interior_critical_point_must_be_included(self):
        x, y = F(1, 4), F(3, 5)
        bounds = delta_range(x, y, (F(1, 4), F(4, 5)))
        critical_value = position(x, ALPHA)-position(y, ALPHA)
        self.assertEqual(bounds[1], critical_value)
        for r in (F(1, 4), F(4, 5)):
            self.assertLess(position(x, r)-position(y, r), bounds[1])

    def test_normalized_endpoint_differences_match_physical_sums(self):
        a, b = (Q(F(1, 3)), Q(F(2, 3))), (Q(F(1, 2)), Q(F(1, 4)))
        for u, v in (('112', '122'), ('11212', '1222'), ('1122', '1222')):
            r, s, h, parity = parameters(u, v)
            lo, hi = difference_range(a, b, (r, r), (s, s), (h, h), parity)
            physical = B(transform(u, a[0])+transform(v, a[1])
                         -transform(u, b[0])-transform(v, b[1]))
            _, _, c, d = matrix(u)
            self.assertEqual(lo, hi)
            self.assertEqual(physical, (-1)**len(u)*lo/(ALPHA*c+d)**2)

    def test_interpolated_endpoints_stay_in_the_correct_child_hull(self):
        for state in ('', '1', '13'):
            a = tail_endpoint(state, '2', False)
            b = tail_endpoint(state, '2', True)
            x = tail_endpoint(state, '2@3/8', False)
            self.assertLess(min(a, b), x)
            self.assertLess(x, max(a, b))
        with self.assertRaises(ValueError):
            tail_endpoint('', '@9/8', False)

    def test_periodic_and_centered_labels_transport_exactly(self):
        for state in ('', '1', '13'):
            self.assertEqual(tail_endpoint(state, '22~2', False), ALPHA)
            self.assertEqual(tail_endpoint(state, '2#1/128', False),
                             transform('2', ALPHA+F(1, 128)))
        with self.assertRaises(ValueError):
            tail_endpoint('13', '1~2', False)
        with self.assertRaisesRegex(ValueError, 'escapes tail hull'):
            tail_endpoint('13', '#1/4', False)


if __name__ == '__main__':
    unittest.main()
