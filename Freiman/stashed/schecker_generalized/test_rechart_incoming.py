import copy
import unittest
from unittest.mock import patch

from explore import Q
from rechart_open_incoming import rechart
from test_piecewise_charts import split_rule
from verify_piecewise_charts import PiecewiseVerifier


class RechartTests(unittest.TestCase):
    def test_offered_only_cut_preserves_roots_but_does_not_claim_old_subtrees(self):
        data,_,_=split_rule()
        targets=set(range(len(data['nodes'])))-set(data['roots'].values())
        result,stats,audit=rechart(data,targets,allow_local=True,offered_only=True)
        self.assertGreater(stats['accepted_edges'],0)
        self.assertFalse(audit['failed_rules'])
        self.assertEqual(len(audit['verified_rules']),len(set(data['roots'].values())))
        self.assertTrue(audit['open_nodes'])
        for name,old in data['roots'].items():
            new=result['nodes'][result['roots'][name]]
            self.assertEqual((new['lower'],new['upper']),
                             (data['nodes'][old]['lower'],data['nodes'][old]['upper']))

    def test_local_subtree_repair_keeps_fresh_successors_unproved(self):
        data,_,_=split_rule();original=copy.deepcopy(data)
        with patch.object(Q,'decimal',side_effect=AssertionError('float in rechart')):
            result,stats,audit=rechart(data,{2},allow_local=True,repair_children=True)
        self.assertEqual(data,original)
        self.assertGreater(stats['accepted_edges'],0)
        self.assertFalse(audit['failed_rules'])
        self.assertTrue(audit['open_nodes'])
        with self.assertRaisesRegex(ValueError,'unresolved'):
            PiecewiseVerifier(result).closed()

    def test_actual_images_preserve_parent_covers_and_unresolved_children(self):
        data,_,_=split_rule();original=copy.deepcopy(data)
        before=PiecewiseVerifier(data).audit()
        with patch.object(Q,'decimal',side_effect=AssertionError('float in rechart')):
            result,stats,audit=rechart(data,set(before['open_nodes']))
        self.assertEqual(data,original)
        self.assertGreater(stats['accepted_edges'],0)
        self.assertEqual(len(audit['verified_rules']),len(before['verified_rules']))
        self.assertFalse(audit['failed_rules'])
        with self.assertRaisesRegex(ValueError,'unresolved'):
            PiecewiseVerifier(result).closed()


if __name__=='__main__':
    unittest.main()
