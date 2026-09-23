import copy
from pathlib import Path
import tempfile
import unittest
from merge_alternative_banks import merge, merge_history
from audit_alternative_bank import supported


class MergeChecks(unittest.TestCase):
    def test_two_open_banks_can_close_only_after_union(self):
        nodes=[dict(id=i,states=['222','222'],parity=1,ratio_bin=0,
                    interval=[i,i+1],covered=False,children=[]) for i in range(3)]
        base=dict(schema='kf131-scalar-atlas-v1',settings=dict(base='.96',bins=72,grid=256,
                  memory=3,max_step=2),root_prefixes=['112222','122222'],roots=[0],
                  nodes=nodes,alternative_rules=[])
        def rule(parent,child):
            return dict(parent=parent,children=[dict(suffixes=['2',''],cases=[dict(
                swap=False,interval=[0,1],destinations=[child])])])
        a,b=copy.deepcopy(base),copy.deepcopy(base)
        a['alternative_rules']=[rule(0,1),rule(0,2)]
        b['alternative_rules']=[rule(1,0),rule(0,2)]
        b['settings']['memory']=5
        self.assertFalse(supported(a)['supported_nodes'])
        self.assertFalse(supported(b)['supported_nodes'])
        result=merge([a,b])
        self.assertEqual(supported(result)['supported_nodes'],[0,1])
        self.assertEqual(len(result['alternative_rules']),3)
        self.assertEqual(result['settings']['memory'],5)
        self.assertFalse(result['closed_candidate'])
        self.assertEqual(len(a['alternative_rules']),2)
        self.assertEqual(merge(iter([a,b])),result)
        b['settings']['grid']=512
        with self.assertRaisesRegex(ValueError,'incompatible geometry'):
            merge([a,b])

    def test_history_pooling_does_not_repeat_shared_attempts(self):
        with tempfile.TemporaryDirectory() as directory:
            a,b,out=[Path(directory)/name for name in ('a','b','out')]
            header='kf131-learning-v1 0.996 512 1024\n'
            key='22222 22222 1 0 0 0 -1 0 '
            extra='22222 22222 1 0 0 0 0 1 '
            a.write_text(header+key+'5\n')
            b.write_text(header+key+'3\n'+extra+'2\n')
            self.assertEqual(merge_history([a,b],out),2)
            self.assertEqual(out.read_text(),header+key+'5\n'+extra+'2\n')
            b.write_text('kf131-learning-v1 0.996 512 2048\n'+key+'3\n')
            with self.assertRaisesRegex(ValueError,'geometry mismatch'):
                merge_history([a,b],out)


if __name__=='__main__': unittest.main()
