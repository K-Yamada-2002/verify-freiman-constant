import copy
import json
from pathlib import Path
import unittest
from fractions import Fraction as F
from explore import hull, Q, matrix, transform
from search_types import Search
from search_shape_bank import ShapeSearch, SHAPES
from exact_shape_search import ExactSearch
from type_certificates import verify, Builder, node_interval
from uniform_initial_cover import compute

HERE=Path(__file__).parent


class TypeSearchChecks(unittest.TestCase):
    def test_uniform_cover_certificate(self):
        result=compute()
        b=result['first_contact_uniform_lower_bound']
        self.assertGreater(Q(F(b['a']),F(b['b'])),0)

    def test_normalized_child_map(self):
        s=Search(1,20)
        for u,v in [('32113','4322'),('3131','3131'),('321','431')]:
            def z(a,b):
                x=Q(F(2,5));y=Q(F(3,7));du=matrix(a)[3]
                return du*du*(transform(a,x)+transform(b,y)-transform(a,Q(0))-transform(b,Q(0)))
            parent=float(z(u,v).decimal())
            # Compare the affine map with directly appending the digit to the tails.
            for uu,vv,off,scale in s.children(u,v):
                child=float(z(uu,vv).decimal())
                du,dv=uu[len(u):],vv[len(v):]
                expected=matrix(u)[3]**2*(transform(u+du,Q(F(2,5)))+
                         transform(v+dv,Q(F(3,7)))-transform(u,Q(0))-transform(v,Q(0)))
                self.assertAlmostEqual(off+scale*child,float(expected.decimal()),places=12)

    def test_shallow_exact_and_float_agree(self):
        exact=ExactSearch();fast=ShapeSearch()
        for u,v in [('32113','4322'),('3131','3131')]:
            for d in range(1,4):
                ex=exact.domain(u,v,d);fl=fast.domain(u,v,d)
                self.assertEqual(len(ex),len(fl))
                base=transform(u,Q(0))+transform(v,Q(0));scale=matrix(u)[3]**2
                for (a,b),(c,e) in zip(ex,fl):
                    self.assertAlmostEqual(float((scale*(a-base)).decimal()),c,places=12)
                    self.assertAlmostEqual(float((scale*(b-base)).decimal()),e,places=12)

    def test_saved_exact_covers(self):
        for name in ('type_certificate.json','type_certificate_depth8.json',
                     'four_shapes_step2_certificate.json'):
            data=json.loads((HERE/name).read_text())
            result=verify(data)
            self.assertEqual(result,data['verification'])
            self.assertGreater(result['unproved_full_hull_leaves'],0)

    def test_replay_rejects_missing_cover(self):
        data=json.loads((HERE/'type_certificate.json').read_text())
        data['nodes'][data['roots'][0]]['children']=[]
        with self.assertRaises(AssertionError):verify(data)

    def test_replay_rejects_shrunken_root(self):
        data=json.loads((HERE/'type_certificate.json').read_text())
        root=data['nodes'][data['roots'][0]]
        root['lower']=list(root['upper'])
        with self.assertRaises(AssertionError):verify(data)

    def test_two_digit_moves_account_for_both_digits(self):
        s=ShapeSearch(max_step=2)
        builder=Builder(s);root=builder.root('32113','4322',3)
        data={'nodes':builder.nodes,'roots':[root],'ratio_bound':20,'depth':3,
              'shape_bank':4,'max_step':2,'horizon_unit':'digits'}
        verify(data)
        for n in data['nodes']:
            if n['remaining_depth']==0:
                self.assertGreaterEqual(len(n['left'])+len(n['right'])-9,3)


if __name__=='__main__':unittest.main()
