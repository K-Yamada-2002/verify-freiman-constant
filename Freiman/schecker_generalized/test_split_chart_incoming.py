import copy
import unittest
from unittest.mock import patch

from explore import Q
from split_chart_incoming import split_incoming
from test_piecewise_charts import split_rule
from verify_piecewise_charts import PiecewiseVerifier


class IncomingSplitTests(unittest.TestCase):
    def test_local_parent_guards_are_clipped_before_leaf_repair(self):
        data, _, _ = split_rule()
        node=data['nodes'][2]
        node['pieces']=[dict(cell=node['cell'],children=node['children'])]
        node['children']=[]
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in split')):
            result, stats, audit=split_incoming(data,[2],allow_local=True)
        self.assertGreater(stats['clones_created'],0)
        self.assertFalse(audit['failed_rules'])
        clones=[n for n in result['nodes'] if n.get('incoming_lineage')==2]
        self.assertTrue(clones)
        self.assertTrue(all(n.get('pieces') for n in clones))

    def test_guarded_incoming_split_preserves_all_rules_and_stays_open(self):
        data, _, _ = split_rule()
        original = copy.deepcopy(data)
        before = PiecewiseVerifier(data).audit()
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in split')):
            result, stats, audit = split_incoming(data, before['open_nodes'])
        self.assertEqual(data, original)
        self.assertGreater(stats['redirected_references'], 0)
        self.assertGreater(stats['clones_created'], 0)
        self.assertFalse(audit['failed_rules'])
        self.assertEqual(len(audit['verified_rules']), len(before['verified_rules']))
        self.assertTrue(audit['open_nodes'])
        self.assertTrue(all(not n.get('children') and not n.get('pieces')
                            for n in result['nodes'] if 'incoming_split_origin' in n))
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            PiecewiseVerifier(result).closed()

    def test_local_and_missing_targets_rejected(self):
        data, _, _ = split_rule()
        for targets in ([data['roots']['zero']], [len(data['nodes'])]):
            with self.assertRaisesRegex(ValueError, 'only unresolved'):
                split_incoming(data, targets)


if __name__ == '__main__':
    unittest.main()
