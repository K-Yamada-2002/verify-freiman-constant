from fractions import Fraction as F
import random
import unittest
from sum_interval_gaps import compact,sum_gaps

class IntervalSumTests(unittest.TestCase):
    def test_against_exact_cartesian_sum(self):
        rng=random.Random(31313)
        for _ in range(150):
            families=[]
            for side in range(2):
                families.append([tuple(sorted((F(rng.randrange(-50,51),16),F(rng.randrange(-50,51),16))))
                                 for j in range(rng.randrange(0,12))])
            left,right=families;lo,hi=F(-2),F(2)
            rows=compact((max(lo,a+c),min(hi,b+d)) for a,b in left for c,d in right)
            expected=[];at=lo
            for a,b in rows:
                if a>at:expected.append((at,a))
                at=max(at,b)
            if at<hi:expected.append((at,hi))
            self.assertEqual(sum_gaps(left,right,(lo,hi)),expected)

    def test_many_separated_cylinders_and_absorbed_gaps(self):
        left=[(F(i,100),F(i,100)+F(1,1000)) for i in range(100)]
        right=[(F(i,10000),F(i,10000)+F(1,20000)) for i in range(200)]
        self.assertEqual(sum_gaps(left,right,(F(0),F(1))),[])

    def test_touching_intervals_and_outer_gaps(self):
        self.assertEqual(sum_gaps([(0,1)],[(0,1),(2,3)],(-1,5)),[(-1,0),(4,5)])
        with self.assertRaises(ValueError):sum_gaps([],[],(1,0))

if __name__=='__main__':unittest.main()
