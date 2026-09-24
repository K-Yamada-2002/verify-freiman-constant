"""Independent rational enclosures and regressions for the exact experiments."""
import unittest
from itertools import product
from explore import *


def rational_cylinder(word):
    # Independent backwards evaluation, without matrix()/transform().
    ends = []
    for tail in (F(0), F(1)):
        for digit in reversed(word):
            tail = 1 / (int(digit) + tail)
        ends.append(tail)
    return min(ends), max(ends)


class ExactChecks(unittest.TestCase):
    def test_quadratic_order_against_integer_sqrt_enclosure(self):
        scale = 10**40
        n = isqrt(462*scale*scale)
        for a in range(-24,25):
            for b in range(-3,4):
                value = Q(a,b)
                ends = [F(a)+b*F(n,scale), F(a)+b*F(n+1,scale)]
                lo, hi = min(ends), max(ends)
                self.assertTrue(lo <= value <= hi)
                if lo > 0:
                    self.assertEqual(value.sign(), 1)
                elif hi < 0:
                    self.assertEqual(value.sign(), -1)
        self.assertLess(Q(-43,2), 0)
        self.assertGreater(Q(-42,2), 0)

    def test_field_and_cf(self):
        for word in ('1','2','3131','321133','43221'):
            value = transform(word,Q(0,1))
            x = Q(0,1)
            for digit in reversed(word):
                x = 1/(int(digit)+x)
            self.assertEqual(x,value)
            self.assertEqual(x/x,1)

    def test_automaton_against_literal_forbidden_words(self):
        for length in range(8):
            for digits in product('123',repeat=length):
                word = ''.join(digits)
                if BAN in word:
                    with self.assertRaises(ValueError):
                        state_of(word)
                else:
                    actual = max((s for s in STATES if word.endswith(s)),key=len)
                    self.assertEqual(state_of(word),actual)

    def test_extrema_independent_rational_enclosures(self):
        for state in STATES:
            for high in (False,True):
                value, pre, period = extreme_tail(state,high)
                stream = pre+period*16
                self.assertNotIn(BAN,state+stream)
                lo,hi = rational_cylinder(stream)
                self.assertLessEqual(lo,value)
                self.assertLessEqual(value,hi)
                self.assertLess(hi-lo,F(1,10**35))
                # Compare all finite 5-digit continuations to the alleged extreme.
                for full in extensions(state,5):
                    suffix = full[len(state):]
                    lower,upper = rational_cylinder(suffix)
                    if high:
                        self.assertGreaterEqual(value,lower)
                    else:
                        self.assertLessEqual(value,upper)

    def test_children_preserve_extrema_and_nesting(self):
        for word in ('3','313','3131','32113','4322'):
            parent = cylinder(word)
            children = [cylinder(w) for w in extensions(word,1)]
            self.assertEqual(min(lo for lo,hi in children),parent[0])
            self.assertEqual(max(hi for lo,hi in children),parent[1])
            for lo,hi in children:
                self.assertTrue(parent[0] <= lo <= hi <= parent[1])

    def test_user_gap_has_simple_endpoint_formulas(self):
        t = Q(-1,F(1,12))
        v = Q(F(-29,53),F(2,53))
        gap = gaps(outer_components('3131','3131',1))[0]
        self.assertEqual(gap[0],2*transform('31312',v))
        self.assertEqual(gap[1],transform('31311',t)+transform('31312',t))
        self.assertLess(gap[0],F(52814,100000))
        self.assertLess(F(52815,100000),gap[1])
        # Rational test points lie inside the parent hull yet outside every child hull.
        target = Q(F(105629,200000))
        lo,hi = hull('3131','3131')
        self.assertTrue(lo < target < hi)
        self.assertFalse(any(lo <= target <= hi
                             for lo,hi in outer_components('3131','3131',1)))

    def test_freiman_endpoint_identity(self):
        cf = Q(F(2221564096,491993569),F(283748,491993569))
        self.assertEqual(4+hull('32113','4322')[0],cf)
        self.assertEqual(4+transform('3211',periodic('313121'))
                         +transform('4322',periodic('313121')),cf)
        self.assertLess(Q(0,F(4,19)),F(113195,25000))
        self.assertLess(F(113195,25000),cf)

    def test_old_ratio_bounds_and_secondary_centres(self):
        for u,v in [('313','312'),('32112','4322')]:
            self.assertGreaterEqual(full_ratio_compare(u,v,F(5,17)),0)
            self.assertLessEqual(full_ratio_compare(u,v,F(17,5)),0)
        self.assertEqual(full_ratio_compare('3131','3131',F(1)),0)
        for u,v in [('321','431'),('32112','4322'),
                    ('32113','4323'),('32113','4322')]:
            bound = 4+cylinder(v[1:])[1]+1/(4+cylinder(u)[0])
            self.assertLess(bound,F(113195,25000))

    def test_periodic_skeleton(self):
        previous = None
        cf = Q(F(2221564096,491993569),F(283748,491993569))
        for n in range(5):
            u,v = '3211'+'313121'*n+'3','4322'+'313121'*n
            lo,hi = hull(u,v)
            self.assertEqual(4+lo,cf)
            if previous:
                self.assertLess(hi,previous)
            previous=hi

    def test_one_step_predicate_really_is_insufficient(self):
        u,v = '321133','43221'
        self.assertTrue(locally_good(u,v))
        self.assertTrue(gaps(outer_components(u,v,3)))
        self.assertFalse(has_cover(u,v,3,locally_good)['covered'])

    def test_returned_cover_can_be_replayed(self):
        u,v = '32113','4322'
        result = has_cover(u,v,3,locally_good)
        self.assertTrue(result['covered'])
        children = result['children']
        for du,dv in children:
            self.assertTrue(du or dv)
            self.assertTrue(locally_good(u+du,v+dv))
        self.assertEqual(merge(hull(u+du,v+dv) for du,dv in children),[hull(u,v)])


if __name__ == '__main__':
    unittest.main()
