import math
import unittest
from fractions import Fraction as Q
from search import (Model, catalogue, cf_bounds, matrix, merge, sum_components,
                    coverage, interface_bound, point_witness, certify_witness)


class SearchTests(unittest.TestCase):
    def test_kf_extrema_against_closed_form(self):
        m=Model('KF',forbidden=('131',))
        lo,hi=m.bounds['']
        self.assertAlmostEqual(lo,(2*math.sqrt(10)-5)/5,14)
        self.assertAlmostEqual(hi,(2*math.sqrt(10)-4)/3,14)
        self.assertIsNone(m.follow('113131'))
        self.assertIsNotNone(m.follow('113231'))

    def test_matrices_against_backward_fraction_evaluation(self):
        for word in ('','1','123','112213','3332121'):
            a,b,c,d=matrix(word)
            ends=sorted((a*x+b)/(c*x+d) for x in (Q(1,4),Q(4,5)))
            self.assertEqual(tuple(ends),cf_bounds(word))
            self.assertEqual(a*d-b*c,(-1)**len(word))

    def test_all_connector_paths_are_legal(self):
        for m in catalogue():
            for s,w in m.connectors.items():
                self.assertIsNotNone(m.follow(w+'2'*20,s))

    def test_model_validation(self):
        with self.assertRaises(ValueError): Model('bad',forbidden=('13',))
        with self.assertRaises(ValueError): Model('bad',forbidden=('22',))

    def test_cylinder_children_nested_and_prefix_checked(self):
        m=Model('KF',forbidden=('131',))
        for z in m.cylinders('',4):
            for c in m.children(z):
                self.assertGreaterEqual(c[3],z[3]-1e-15)
                self.assertLessEqual(c[4],z[4]+1e-15)
        with self.assertRaises(ValueError): m.cylinder('131')

    def test_merge_keeps_small_gaps_and_accepts_mixed_sequences(self):
        self.assertEqual(merge([[0,1],(1,2),(2.00000000001,3)]),[[0,2],[2.00000000001,3]])

    def test_budget_is_not_success_and_known_gap(self):
        m=Model('12','12')
        r=coverage(m,m,'','',[1.2,1.3],1e-8,1)
        self.assertEqual(r['status'],'budget_exhausted')
        r=coverage(m,m,'1','1',[.1,.2],1e-8,100)
        self.assertEqual(r['status'],'gap_float')

    def test_background_and_interface_bounds(self):
        m=Model('KF',forbidden=('131',))
        b,w=m.background(3)
        self.assertGreater(float(b),4*math.sqrt(10)/3)
        self.assertLess(float(b),4.22)
        self.assertNotIn('131',w)
        self.assertEqual(interface_bound('1111','1222'),Q(18,5))
        self.assertGreater(interface_bound('1311','1211'),Q(18,5))

    def test_exact_witness_and_rejection(self):
        m=Model('KF',forbidden=('131',))
        target=Q('1.29289')
        w=point_witness(m,m,'112','122',target,25,20000)
        self.assertIsNotNone(w)
        a,b=certify_witness(m,w['u'],'112')
        c,d=certify_witness(m,w['v'],'122')
        self.assertLess(max(abs(a+c-target),abs(b+d-target)),Q(1,10**25))
        with self.assertRaises(ValueError): certify_witness(m,'131','1')
        with self.assertRaises(ValueError): certify_witness(m,w['u'],'122')
        f=Model('no232',forbidden=('232',))
        with self.assertRaises(ValueError): certify_witness(f,'23','2')


if __name__=='__main__': unittest.main()
