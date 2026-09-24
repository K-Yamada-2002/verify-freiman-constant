import unittest

from exact import F
from scalar_geometry import quadratic_parameters
from sloped_scalar_geometry import band_endpoint
from fast_return_kernel import endpoint,intersect


class FastKernelTests(unittest.TestCase):
    def test_intersections_keep_all_components(self):
        self.assertEqual(intersect([(0,10),(11,14)],[(2,4),(6,12)]),[(2,4),(6,10),(11,12)])

    def test_float_endpoint_matches_exact_band_bounds(self):
        rb,sb,hb=(F(1,4),F(4,5)),(F(2,5),F(1,2)),(F(1,3),F(2,3))
        def quad(word,box):
            b,a,ts=quadratic_parameters(word,box)
            return [float(x.decimal()) for x in (b,a,*ts)]
        move=[quad('13',rb),quad('2',sb),1,-1,[]]
        for p in (-1,1):
            parent=dict(parity=p,hbox=list(map(float,hb)),slope=-.25)
            for swap in (False,True):
                got=endpoint(parent,move,swap,-.2,.125)
                expected=band_endpoint('13','2',swap,F(-1,5),F(1,8),F(-1,4),rb,sb,hb,p)
                for a,b in zip(got,expected): self.assertAlmostEqual(a,float(b.decimal()),places=12)


if __name__=='__main__': unittest.main()
