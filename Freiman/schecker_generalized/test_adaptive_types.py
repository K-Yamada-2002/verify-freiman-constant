import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from adaptive_types import (F, Q, AdaptiveSearch, affine_rows, comparison_polynomial,
                            full_labels, ge, label_value, quadratic_minimum,
                            sample_ge, verify_row, word_pair,uniform_width_ratio)
from explore import matrix
from adaptive_induction import verify as verify_certificate,audit_obstructions,combine_cases,Synthesis

HERE=Path(__file__).parent


class AdaptiveTypeChecks(unittest.TestCase):
    def test_saved_certificates_replay_without_discovery_or_decimals(self):
        with patch('adaptive_types.numeric_gap_candidates',side_effect=AssertionError('discovery called')), \
             patch('explore.Q.decimal',side_effect=AssertionError('decimal conversion called')):
            for depth in (4,6,8):
                data=json.loads((HERE/f'adaptive_depth{depth}_certificate.json').read_text())
                result=verify_certificate(data)
                self.assertGreater(result['unproved_terminal_intervals'],0)

    def test_certificate_rejects_missing_cover_and_wrong_horizon(self):
        data=json.loads((HERE/'adaptive_depth4_certificate.json').read_text())
        missing=copy.deepcopy(data);missing['nodes'][missing['root']]['children']=[]
        with self.assertRaises(AssertionError):verify_certificate(missing)
        shallow=copy.deepcopy(data)
        child=shallow['nodes'][shallow['root']]['children'][0]['node']
        shallow['nodes'][child]['remaining_depth']+=1
        with self.assertRaises(AssertionError):verify_certificate(shallow)

    def test_parameter_case_certificate_must_cover_zero_and_positive(self):
        source=json.loads((HERE/'adaptive_depth4_certificate.json').read_text())
        cases=[]
        for regime in ('zero','positive'):
            case=copy.deepcopy(source);case['regime']=regime
            for row in case['nodes']:row['regime']=regime
            cases.append(case)
        combined=combine_cases(cases)
        self.assertTrue(verify_certificate(combined)['all_nonnegative_exponents_verified'])
        missing=copy.deepcopy(combined);missing['cases'].pop()
        with self.assertRaises(AssertionError):verify_certificate(missing)
        repeated=copy.deepcopy(combined);repeated['cases'][1]=repeated['cases'][0]
        with self.assertRaises(AssertionError):verify_certificate(repeated)

    def test_failed_search_keeps_only_replayable_local_seed_rules(self):
        source=json.loads((HERE/'adaptive_depth4_certificate.json').read_text())
        synthesis=Synthesis()
        synthesis.nodes=[source['nodes'][source['root']]]
        failed=synthesis.certificate(None,4)
        self.assertIsNone(failed['root'])
        self.assertEqual(len(failed['partial_local_rules']),1)
        self.assertNotIn('node',failed['partial_local_rules'][0]['children'][0])
        self.assertTrue(Synthesis(seed=failed).seeds)
        broken=copy.deepcopy(failed);broken['partial_local_rules'][0]['children']=[]
        with self.assertRaises(AssertionError):Synthesis(seed=broken)
        with self.assertRaises(AssertionError):verify_certificate(failed)

    def test_discovered_bridge_requires_a_parameter_case_split(self):
        # Components produced by the common-chain depth-eight refinement.
        a,b=full_labels('','')
        pieces=[(a,('3131',True,'1313',False)),
                (('3132',False,'',True),('31',True,'13',False)),
                (('',False,'1312',True),b)]
        for regime,chain in [('zero',[0,1,2]),('positive',[0,2])]:
            current=a
            for i in chain:
                lo,hi=pieces[i]
                self.assertTrue(ge('','',current,lo,regime))
                self.assertTrue(ge('','',hi,current,regime))
                current=hi
            self.assertTrue(ge('','',current,b,regime))
        self.assertFalse(ge('','',pieces[0][1],pieces[2][0],'zero'))
        self.assertFalse(ge('','',pieces[0][1],pieces[1][0],'positive'))
        self.assertGreater(quadratic_minimum(
            comparison_polynomial('','',pieces[1][0],pieces[0][1])),0)

    def test_selected_types_avoid_the_known_exact_gaps(self):
        gaps=json.loads((HERE/'induction_obstructions.json').read_text())['obstructions']
        for depth in (6,8):
            data=json.loads((HERE/f'adaptive_depth{depth}_certificate.json').read_text())
            self.assertEqual(audit_obstructions(data,gaps),[])

    def test_quadratic_minimum_includes_an_interior_vertex(self):
        self.assertEqual(quadratic_minimum((Q(F(1,4)),Q(-1),Q(1)),F(0),F(1)),Q(0))
        self.assertLess(quadratic_minimum((Q(0),Q(0,F(-1,25)),Q(1)),F(0),F(1)),0)
        self.assertEqual(quadratic_minimum((Q(2),Q(-3),Q(0)),F(0),F(1)),Q(-1))

    def test_correlated_polynomial_matches_independent_matrix_evaluation(self):
        first=('1312',False,'2',True)
        second=('2',True,'13',False)
        for u,v in [('', ''),('33','12'),('11','1')]:
            coefficients=comparison_polynomial(u,v,first,second)
            prev,current=0,1
            for n in range(1,7):
                z=F(prev,current)
                polynomial=sum(c*z**i for i,c in enumerate(coefficients))
                x,y=label_value(u,v,first);xx,yy=label_value(u,v,second)
                left,right=word_pair(u,v,n)
                _,_,c,d=matrix(left);_,_,cc,dd=matrix(right)
                p=(-1)**(len(left)+len(right))
                actual=(x-xx)*(dd+cc*y)*(dd+cc*yy)+p*(y-yy)*(d+c*x)*(d+c*xx)
                self.assertEqual(actual,polynomial*current**2)
                self.assertEqual(sample_ge(u,v,first,second,n),polynomial>=0)
                prev,current=current,86*current-prev

    def test_arbitrary_long_endpoint_labels_are_checked_for_legality(self):
        lo,hi=full_labels('','')
        illegal=('1313',False,'',False)  # Left root already ends in 3.
        with self.assertRaises(ValueError):
            ge('','',illegal,hi)
        with self.assertRaises(AssertionError):
            ge('','',('4',False,'',False),hi)

    def test_width_bound_rejects_one_sided_escape(self):
        self.assertTrue(uniform_width_ratio('',''))
        self.assertFalse(uniform_width_ratio('111111',''))

    def test_uniform_replay_rejects_a_missing_child(self):
        # A short exact split with no floating discovery dependency.
        u,v='2',''
        parent=full_labels(u,v)
        children=[]
        for digit in '321':
            children.append({'suffixes':('',digit),'endpoints':full_labels(u,v+digit)})
        row={'left_suffix':u,'right_suffix':v,'endpoints':parent,
             'regime':'all','children':children}
        # Pick the normalized order explicitly.
        from adaptive_types import point,lifted
        row['children'].sort(key=lambda c:min(point(u,v,lifted(*c['suffixes'],z)) for z in c['endpoints']))
        verify_row(row)
        broken=copy.deepcopy(row);broken['children']=[]
        with self.assertRaises(AssertionError):verify_row(broken)


if __name__=='__main__':unittest.main()
