import contextlib
import copy
import io
import json
from pathlib import Path
import unittest

from exact import F,state_of
from explore_return_domains import enlarge
from search_return_kernel import search,inward_union
from verify_scalar_graph import ScalarVerifier


class DomainSearchTests(unittest.TestCase):
    def test_subgrid_overlap_is_merged_before_rounding(self):
        offers=[(F(0),F(7,5)),(F(13,10),F(3))]
        self.assertEqual(inward_union(offers,1),[(0,3)])

    def test_enlargement_covers_old_domains_and_preserves_actual_seed(self):
        p=Path(__file__).parent/'periodic_memory4_partition_current_20260924.json'
        source=json.loads(p.read_text()); saved=copy.deepcopy(source)
        result=enlarge(source,2,0,2,True,'0.96')
        self.assertEqual(source,saved)
        self.assertTrue(all(not n['covered'] and not n['children'] for n in result['nodes']))
        before,after=ScalarVerifier(source),ScalarVerifier(result)
        self.assertEqual(before.seed(),after.seed())
        for i,n in enumerate(source['nodes']):
            rb,sb,hb=before.box(i); candidates=[]
            for j,m in enumerate(result['nodes']):
                r,s,h=after.box(j)
                if (m['parity']==n['parity'] and
                    tuple(map(state_of,m['states']))==tuple(map(state_of,n['states'])) and
                    r[0]<=rb[0]<=rb[1]<=r[1] and s[0]<=sb[0]<=sb[1]<=s[1]):
                    candidates.append(h)
            after.covers_ratio(hb,candidates)

    def test_memory_one_is_rejected_because_it_loses_forbidden_word_state(self):
        with self.assertRaises(ValueError):
            enlarge({},memory=1)

    def test_kernel_does_not_certify_a_single_contracting_return(self):
        p=Path(__file__).parent/'periodic_return_seed_20260924.json'
        with contextlib.redirect_stdout(io.StringIO()):
            _,report=search(json.loads(p.read_text()),length=2,iterations=20)
        self.assertFalse(report['closed'])
        self.assertEqual(report['reason'],'empty')

    def test_checkpoint_cannot_widen_the_root_obligation(self):
        p=Path(__file__).parent/'periodic_return_seed_20260924.json'
        data=json.loads(p.read_text())
        invalid=dict(history=[],intervals=[[[-10**30,10**30]]])
        with self.assertRaises(ValueError):
            search(data,length=2,initial=invalid)


if __name__=='__main__':
    unittest.main()
