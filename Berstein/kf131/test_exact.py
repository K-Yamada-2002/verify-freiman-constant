import unittest
from itertools import product
from exact import F, Q, STATES, state_of, extreme_tail, transform, cylinder
from verify import verify_facts, exclusion, replay_exclusion


class ExactChecks(unittest.TestCase):
    def test_automaton_against_literal_words(self):
        for n in range(8):
            for digits in product('123', repeat=n):
                w = ''.join(digits)
                if '131' in w:
                    with self.assertRaises(ValueError):
                        state_of(w)
                else:
                    state_of(w)

    def test_extrema_against_independent_rational_cylinders(self):
        for state in STATES:
            for high in (False, True):
                value, pre, period = extreme_tail(state, high)
                w = pre+period*40
                self.assertNotIn('131', state+w)
                lo, hi = sorted(transform(w, z) for z in (F(1, 4), F(4, 5)))
                self.assertLess(lo, value)
                self.assertLess(value, hi)
                self.assertLess(hi-lo, F(1, 10**30))

    def test_children_nested_and_shape_bounds(self):
        for n in range(1, 6):
            for digits in product('123', repeat=n):
                w = ''.join(digits)
                if '131' in w:
                    continue
                parent = cylinder(w[:-1])
                child = cylinder(w)
                self.assertLessEqual(parent[0], child[0])
                self.assertLessEqual(child[1], parent[1])

    def test_exact_facts_and_exclusion_replay(self):
        result = verify_facts()
        self.assertEqual(result['uniform_thickness_upper_bound']['a'], '19/4')

    def test_corrupted_certificate_rejected(self):
        target = (F('1.2924533'), F('1.2924537'))
        nodes = exclusion('1122', '122', target)
        nodes[0]['children'].pop()
        with self.assertRaises(AssertionError):
            replay_exclusion(nodes, target)


if __name__ == '__main__':
    unittest.main()
