import copy
import itertools
import json
from pathlib import Path
import unittest
from fractions import Fraction as F
from explore import Q, matrix
from uniform_initial_cover import params
from child_family_covers import parameter_domains, word_pair, verify_row
from invariant_boxes import minimum_difference
from audit_child_covers import audit, canonical

HERE = Path(__file__).parent
FILES = ('child_family_covers.json', 'child_family_covers_deep.json',
         'child_J1_covers.json', 'child_J2R_covers.json', 'child_repair.json',
         'child_H11_1_cover.json', 'child_frontier_covers.json')


class ChildCoverChecks(unittest.TestCase):
    def test_exact_replay_all_saved_rules(self):
        for name in FILES:
            for row in json.loads((HERE/name).read_text())['covers']:
                verify_row(row)

    def test_box_minimum_against_all_corners(self):
        box = ((F(1,4),F(1,3)),(F(2,5),F(3,4)),(F(2,3),F(5,6)))
        for p in (-1,1):
            for a,b in (((Q(F(1,3)),Q(F(2,3))),(Q(F(1,2)),Q(F(1,4)))),
                        ((Q(F(3,4)),Q(F(1,4))),(Q(F(1,5)),Q(F(1,2))))):
                values=[]
                for r,s,q in itertools.product(*box):
                    def value(z):return z[0]/(1+r*z[0])+p*q*z[1]/(1+s*z[1])
                    values.append(value(a)-value(b))
                self.assertEqual(minimum_difference(a,b,*box,p,exact=True),min(values))

    def test_affine_family_enclosure_consistency(self):
        for u,v in (('1',''),('2',''),('3','1'),('31','1')):
            point,box = parameter_domains(u,v)
            for n in range(6):
                left,right=word_pair(u,v,n)
                actual=params(matrix(left),matrix(right))
                domain=point if n==0 else box
                for z,(lo,hi) in zip(actual,domain):
                    self.assertLessEqual(lo,z)
                    self.assertLessEqual(z,hi)

    def test_replay_rejects_uncovered_parent(self):
        row=copy.deepcopy(json.loads((HERE/FILES[1]).read_text())['covers'][0])
        row['children']=[]
        with self.assertRaises(AssertionError):verify_row(row)

    def test_periodic_return_and_missing_obligations(self):
        self.assertEqual(canonical('1312132','3131211',4),('2','1',4))
        documents=[json.loads((HERE/name).read_text()) for name in FILES[:4]+FILES[5:]]
        result=audit(documents)
        self.assertFalse(result['closed_under_children'])
        self.assertEqual(result['reachable_rules'],20)
        self.assertEqual(len(result['unproved_frontier']),36)


if __name__=='__main__':unittest.main()
