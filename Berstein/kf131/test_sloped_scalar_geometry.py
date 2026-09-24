import copy
import json
from pathlib import Path
import unittest

from exact import F,Q,extreme_tail,state_of,transform
from anchored_geometry import ALPHA,B,parameters,position
from repair_gap_intervals import rounded
from scalar_geometry import endpoint_image
from sloped_scalar_geometry import band_endpoint,SlopedScalarVerifier
from verify_scalar_graph import ScalarVerifier,verifier_for


def centered(x,y,r,s,h,p):
    return position(x,r)-position(ALPHA,r)+p*h*(position(y,s)-position(ALPHA,s))


class SlopedGeometryTests(unittest.TestCase):
    def test_point_transport_against_actual_continued_fractions(self):
        for left,right in [('11222','12222'),('1122','12222')]:
            r,s,h,p=parameters(left,right)
            for u,v in [('1',''),('','3'),('2','2'),('12','3'),('3','12')]:
                rr,ss,hh,pp=parameters(left+u,right+v)
                x=extreme_tail(state_of(left+u),False)[0]
                y=extreme_tail(state_of(right+v),True)[0]
                for swap in (False,True):
                    k,K=F(1,7),F(-2,9)
                    child=centered(y,x,ss,rr,1/hh,pp)-k/hh if swap else centered(x,y,rr,ss,hh,pp)-k*hh
                    expected=centered(transform(u,x),transform(v,y),r,s,h,p)-K*h
                    got=band_endpoint(u,v,swap,child,k,K,(r,r),(s,s),(h,h),p)
                    self.assertEqual(got,(expected,expected))

    def test_zero_slope_is_the_old_full_box_formula(self):
        rb,sb,hb=(F(1,4),F(4,5)),(F(2,5),F(1,2)),(F(1,3),F(2,3))
        for p in (-1,1):
            for swap in (False,True):
                self.assertEqual(band_endpoint('13','2',swap,F(-1,5),0,0,rb,sb,hb,p),
                                 endpoint_image('13','2',swap,F(-1,5),rb,sb,hb,p))

    def test_nonzero_slope_full_box_bounds_include_interior_samples(self):
        rb,sb,hb=(F(1,4),F(4,5)),(F(2,5),F(1,2)),(F(1,3),F(2,3))
        for p in (-1,1):
            for swap in (False,True):
                lo,hi=band_endpoint('13','2',swap,F(-1,5),F(1,8),F(-1,4),rb,sb,hb,p)
                for t in (F(0),F(1,3),F(1,2),F(1)):
                    r=rb[0]+t*(rb[1]-rb[0]); s=sb[0]+(1-t)*(sb[1]-sb[0]); h=hb[0]+t*(hb[1]-hb[0])
                    a,b=band_endpoint('13','2',swap,F(-1,5),F(1,8),F(-1,4),(r,r),(s,s),(h,h),p)
                    self.assertLessEqual(lo,a); self.assertLessEqual(b,hi)

    def test_sloped_seed_contains_the_direct_all_two_tail_sum(self):
        d=json.loads((Path(__file__).parent/'periodic_return_seed_20260924.json').read_text())
        d['schema']='kf131-sloped-atlas-v1'; root=d['roots'][0]; u,v=d['root_prefixes']
        h=parameters(u,v)[2]; grid=d['settings']['grid']; t=-F(1,4)*h
        for n in d['nodes']: n['scalar_slope']='1/4'
        d['nodes'][root]['interval']=[rounded(t,grid,False)-2,rounded(t,grid,True)+2]
        verifier=SlopedScalarVerifier(d); verifier.check_initial_hull(root)
        def decode(x): return B(Q(F(x['a']['a']),F(x['a']['b'])),Q(F(x['b']['a']),F(x['b']['b'])))
        lo,hi=map(decode,verifier.seed()); direct=transform(u,ALPHA)+transform(v,ALPHA)
        self.assertLess(lo,direct); self.assertLess(direct,hi)

    def test_schema_and_mixed_slopes_cannot_silently_use_constant_cover(self):
        d=json.loads((Path(__file__).parent/'periodic_return_seed_20260924.json').read_text())
        old=ScalarVerifier(d); d['schema']='kf131-sloped-atlas-v1'
        for n in d['nodes']: n['scalar_slope']='0'
        with self.assertRaises(ValueError): ScalarVerifier(d)
        new=verifier_for(d)
        self.assertEqual(new.seed(),old.seed())
        self.assertEqual(new.initial_hull(0),old.initial_hull(0))
        d['nodes'].append(dict(copy.deepcopy(d['nodes'][0]),scalar_slope='1/4'))
        with self.assertRaises(ValueError):
            SlopedScalarVerifier(d).transport(0,'2','2',False,(F(0),F(1)),[0,1])


if __name__=='__main__': unittest.main()
