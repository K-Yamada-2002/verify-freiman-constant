import unittest

from exact import F, extreme_tail, matrix, state_of, transform
from anchored_geometry import ALPHA, B, parameters, position
from scalar_geometry import endpoint_image, quadratic_range, uniform_child_core


def centered(x, y, r, s, h, p):
    return position(x, r)-position(ALPHA, r)+p*h*(position(y, s)-position(ALPHA, s))


class ScalarGeometryChecks(unittest.TestCase):
    def test_transports_agree_with_actual_prefixes_and_exchange(self):
        for left, right in [('11222', '12222'), ('1122', '12222')]:
            r, s, h, p = parameters(left, right)
            for u, v in [('1', ''), ('', '3'), ('2', '2'), ('12', '3'), ('3', '12')]:
                rr, ss, hh, pp = parameters(left+u, right+v)
                x = extreme_tail(state_of(left+u), False)[0]
                y = extreme_tail(state_of(right+v), True)[0]
                expected = centered(transform(u, x), transform(v, y), r, s, h, p)
                for swap in (False, True):
                    value = centered(y, x, ss, rr, 1/hh, pp) if swap else centered(x, y, rr, ss, hh, pp)
                    bounds = endpoint_image(u, v, swap, value, (r, r), (s, s), (h, h), p)
                    self.assertEqual(bounds, (expected, expected))

    def test_common_two_has_constant_gain_and_zero_translation(self):
        interval = F(-1, 7), F(2, 7)
        for p in (-1, 1):
            core = uniform_child_core('2', '2', False, interval,
                                       (F(1, 4), F(4, 5)), (F(1, 3), F(1, 2)),
                                       (F(1, 3), F(2, 3)), p)
            self.assertEqual(core, tuple(-t/(2+ALPHA)**2 for t in interval[::-1]))

    def test_quadratic_vertex_is_included(self):
        word, rb = '1', (F(1, 4), F(4, 5))
        _, _, c, d = matrix(word)
        z, denominator = transform(word, ALPHA), c*ALPHA+d
        ts = [(1+r*ALPHA)/(1+r*z) for r in rb]
        vertex = sum(ts, B())/2
        k = -(z-ALPHA)*denominator**2/(2*vertex)
        low, high = quadratic_range(word, k, rb)
        f = lambda t: (z-ALPHA)*t+k*t*t/(denominator**2)
        self.assertEqual(high, f(vertex))
        self.assertGreater(high, max(map(f, ts)))
        self.assertEqual(low, min(map(f, ts)))

    def test_full_box_bounds_contain_interior_samples(self):
        rb, sb, hb = (F(1, 4), F(4, 5)), (F(2, 5), F(1, 2)), (F(1, 3), F(2, 3))
        for swap in (False, True):
            lo, hi = endpoint_image('13', '2', swap, F(-1, 5), rb, sb, hb, -1)
            for i in range(7):
                r = rb[0]+(rb[1]-rb[0])*F(i, 6)
                s = sb[0]+(sb[1]-sb[0])*F(6-i, 6)
                h = hb[0]+(hb[1]-hb[0])*F(i, 6)
                value = endpoint_image('13', '2', swap, F(-1, 5), (r, r), (s, s), (h, h), -1)[0]
                self.assertLessEqual(lo, value)
                self.assertLessEqual(value, hi)


if __name__ == '__main__':
    unittest.main()
