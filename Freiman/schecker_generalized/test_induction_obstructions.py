import copy
import json
import unittest

from audit_child_covers import audit
from child_family_covers import verify_row, word_pair
from explore import Q,F
from frontier_obstructions import COVER_FILES, HERE, target_interval, verify_gap
from periodic_anchor_invariant import verify as verify_anchor_invariant,anchored_difference_range


class InductionObstructionChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.obstructions = json.loads((HERE/'induction_obstructions.json').read_text())['obstructions']

    def test_saved_gaps_exclude_all_legal_cylinder_pairs(self):
        for row in self.obstructions:
            with self.subTest(family=(row['left_suffix'], row['right_suffix'], row['kind'])):
                verify_gap(row)

    def test_widening_gap_over_attained_boundary_is_rejected(self):
        row = copy.deepcopy(self.obstructions[0])
        a, b = word_pair(row['left_suffix'], row['right_suffix'], row['n'])
        tlo, _ = target_interval(a, b, row['kind'])
        lo = Q(row['gap'][0]['a'], row['gap'][0]['b'])
        self.assertLess(tlo, lo)
        row['gap'][0] = ((lo+tlo)/2).record()
        with self.assertRaises(AssertionError):
            verify_gap(row)

    def test_repaired_uniform_covers_remove_known_obstructions(self):
        repairs = json.loads((HERE/'gap_repaired_covers.json').read_text())
        for row in repairs['covers']:
            verify_row(row)
        result = audit([json.loads((HERE/name).read_text()) for name in COVER_FILES]+[repairs], self.obstructions)
        reached = {tuple(key) for edge in result['edges'] for key in edge}
        bad = {(r['left_suffix'], r['right_suffix'], r['kind']) for r in self.obstructions}
        self.assertFalse(reached & bad)
        self.assertFalse(result['known_refuted_obligations'])
        self.assertFalse(result['closed_under_children'])

    def test_old_audit_reports_refuted_obligations(self):
        result = audit([json.loads((HERE/name).read_text()) for name in COVER_FILES], self.obstructions)
        self.assertEqual(len(result['known_refuted_obligations']), 7)

    def test_periodic_phases_share_the_exact_eigenvalue(self):
        verify_anchor_invariant()

    def test_extremal_anchor_difference_has_exact_endpoint_bounds(self):
        from invariant_boxes import STATES,RANGES,tail_endpoint
        for state,(lo,hi) in zip(STATES,RANGES):
            x=tail_endpoint(state,'1',False);y=tail_endpoint(state,'2',True)
            for high in (False,True):
                anchor=tail_endpoint(state,'',high)
                a,b=anchored_difference_range(anchor,x,y,lo,hi)
                for t in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
                    r=lo+(hi-lo)*t
                    value=(x-y)*(1+anchor*r)*(1+anchor*r)/((1+x*r)*(1+y*r))
                    self.assertLessEqual(a,value);self.assertLessEqual(value,b)
                cc,beta=2*anchor-x-y,anchor*(x+y)-2*x*y
                self.assertTrue(cc>=0 and beta>=0 if high else cc<=0 and beta<=0)
            with self.assertRaises(AssertionError):
                anchored_difference_range((x+y)/2,x,y,lo,hi)


if __name__ == '__main__':
    unittest.main()
