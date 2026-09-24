import unittest
from fractions import Fraction as Q
from target_cover import (ThresholdModel,window_library,rational_bounds,
    near_bounds,scan,complement,insert_interval,transform_bounds)

class TargetCoverTests(unittest.TestCase):
    def test_window_upper_and_reverse_symmetry(self):
        m=ThresholdModel(3,2,Q('4.1'))
        self.assertEqual({s[::-1] for s in m.core},m.core)
        for s,a,t,b in window_library(3,2):
            if s in m.core and (a,t) in m.edges[s]:
                self.assertLessEqual(b,m.threshold)
                rev=(s+a)[::-1]
                self.assertIn((rev[-1],rev[1:]),m.edges[rev[:-1]])

    def test_connectors_and_decimal_enclosures(self):
        m=ThresholdModel(4,2,Q('4.49'))
        for s in m.states:
            self.assertEqual(m.follow(m.connectors[s]+'2'*8,s),m.reset)
            a,b=m.cert_bounds[s];x,y=m.bounds[s]
            self.assertLessEqual(float(a),x+1e-14)
            self.assertGreaterEqual(float(b),y-1e-14)

    def test_independent_cf_calculation(self):
        for D in (3,4):
            for word in ('','1','4123','112112'):
                self.assertEqual(rational_bounds(word,D),transform_bounds(word,(Q(1,D+1),Q(D+1,D+2))))

    def test_interval_union_does_not_close_small_gaps(self):
        cs=[];starts=[]
        for a,b in [(1,2),(3,4),(2,2.99),(0,1)]:insert_interval(cs,starts,a,b)
        self.assertEqual(cs,[[0,2.99],[3,4]])
        self.assertEqual(complement(cs,0,4),[[2.99,3]])

    def test_cover_metadata_and_exact_dominance(self):
        m=ThresholdModel(4,2,Q('4.09999'))
        result=scan(m,[4.1,4.1001],1e-6,20000,rational_leaves=True)
        self.assertEqual(result['status'],'covered_float')
        self.assertEqual(result['rational_leaf_check']['gaps'],[])
        self.assertLessEqual(Q(result['rational_leaf_check']['maximum_sum_hull_width']),Q('0.000001'))
        self.assertFalse(complement([z for c in result['candidates'] for z in c['intervals']],4.1,4.1001))
        for c in result['candidates']:
            _,hi=near_bounds(c['u'],c['v'],c['center'],2,4,True,m)
            self.assertEqual(hi,Q(c['near_bound']))
            self.assertLessEqual(hi,m.threshold)
        self.assertEqual(scan(m,[4.1,4.11],1e-8,1)['status'],'budget_exhausted')

if __name__=='__main__':unittest.main()
