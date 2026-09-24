import itertools
import unittest
from fractions import Fraction as Q
from reduce_cover import antichain,dominance,interval_cover,scan_product,same_language
from target_cover import ThresholdModel,complement

class ReductionTests(unittest.TestCase):
    def test_prefix_antichain(self):
        self.assertEqual(antichain(['112','11','2','21','11']),('11','2'))

    def test_interval_greedy_matches_exhaustive_minimum(self):
        options=[(0,.4,0),(0,.6,1),(.3,.7,2),(.5,1,3),(.6,.9,4)]
        selected,gaps=interval_cover(options,0,1)
        self.assertFalse(gaps)
        minimum=min(k for k in range(1,len(options)+1)
                    if any(not complement([(a,b) for a,b,i in subset],0,1)
                           for subset in itertools.combinations(options,k)))
        self.assertEqual(len(selected),minimum)
        _,gaps=interval_cover([(0,.4,0),(.4000000001,1,1)],0,1)
        self.assertEqual(gaps,[[.4,.4000000001]])

    def test_cross_pairs_must_be_checked(self):
        m=ThresholdModel(4,2,Q('4.50999'))
        # The whole shift allows a central exception that can create a larger
        # nearby peak, so replacing every factor by the whole shift is unsafe.
        self.assertGreater(dominance(m,('1','2','3'),('1','2','3')),Q('4.52'))
        self.assertLess(dominance(m,('11','12'),('11','12')),Q('4.1'))

    def test_distinct_presentations_of_same_cantor_set(self):
        higher=ThresholdModel(4,4,Q('4.233'))
        lower=ThresholdModel(4,3,Q('4.24'))
        self.assertNotEqual(higher.graph_signature,lower.graph_signature)
        equal,states=same_language(higher,lower)
        self.assertTrue(equal)
        self.assertGreater(states,len(lower.core))
        different=ThresholdModel(4,3,Q('4.22'))
        self.assertFalse(same_language(lower,different)[0])

    def test_one_product_rational_cover_and_budget(self):
        m=ThresholdModel(4,2,Q('4.09999'))
        r=scan_product(m,('21',),('12',),[4.1,4.1001],1e-6,20000,True)
        self.assertEqual(r['status'],'completed_float')
        self.assertEqual(r['gaps'],[])
        q=[list(map(Q,x)) for x in r['rational_leaf_check']['covered']]
        self.assertEqual(complement(q,Q('4.1'),Q('4.1001')),[])
        self.assertLessEqual(Q(r['rational_leaf_check']['maximum_width']),Q('0.000001'))
        r=scan_product(m,('21',),('12',),[4.1,4.11],1e-8,1)
        self.assertEqual(r['status'],'budget_exhausted')

if __name__=='__main__':unittest.main()
