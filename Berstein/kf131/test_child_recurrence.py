import unittest
from exact import F, matrix, state_of
from type_certificates import endpoint
from uniform_cover import ROOT
from child_recurrence import compute, RETURN, OFFERS, PREFIXES


def in_domain(u, v):
    _, _, cu, du = matrix(u)
    _, _, cv, dv = matrix(v)
    r, s, q = F(cu, du), F(cv, dv), F(du*du, dv*dv)
    return (state_of(u) == state_of(v) == '' and len(u) % 2 == len(v) % 2
            and F(9, 25) <= r <= F(9, 20) and F(9, 25) <= s <= F(9, 20)
            and F(489, 1000) <= q <= F(512, 1000)
            and F(489, 1000) <= q*((1+r)/(1+s))**2 <= F(512, 1000))


class ChildRecurrenceChecks(unittest.TestCase):
    def test_uniform_inequalities(self):
        data = compute()
        self.assertEqual(data['return_offer_index'], 4)
        self.assertEqual(len(data['checks']), 19)

    def test_return_is_the_same_root_interval(self):
        lhs = [endpoint('112', '122', e) for e in RETURN]
        rhs = sorted(endpoint('1122', '1222', e) for e in ROOT)
        self.assertEqual(lhs, rhs)
        self.assertTrue(in_domain('1122', '1222'))

    def test_common_word_domain_and_nested_return_family(self):
        pairs = [('112', '122')]
        for _ in range(5):
            new = []
            for u, v in pairs:
                self.assertTrue(in_domain(u, v))
                for w in ('2', '12'):
                    self.assertTrue(in_domain(u+w, v+w))
                    new.append((u+w, v+w))
                lo, hi = sorted(endpoint(u, v, e) for e in ROOT)
                a, b = sorted(endpoint(u+'2', v+'2', e) for e in ROOT)
                self.assertLess(lo, a)
                self.assertLess(b, hi)
            pairs = new

    def test_offer_endpoints_extend_their_declared_prefixes(self):
        for (lo, hi), (u, v) in zip(OFFERS, PREFIXES):
            for su, h, sv, k in (lo, hi):
                self.assertTrue(su.startswith(u))
                self.assertTrue(sv.startswith(v))
                state_of(su)
                state_of(sv)


if __name__ == '__main__':
    unittest.main()
