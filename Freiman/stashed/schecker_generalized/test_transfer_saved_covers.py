import copy,json
from pathlib import Path
import unittest
from transfer_saved_covers import transfer
from verify_piecewise_charts import PiecewiseVerifier

class TransferTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        old=json.loads((Path(__file__).parent/'schecker_return_current_20260924.json').read_text())
        ids=list(dict.fromkeys([0,1]+[d['node'] for n in old['nodes'][:2] for e in n['children'] for d in e['destinations']]))
        mapping={v:i for i,v in enumerate(ids)};nodes=[]
        for i in ids:
            n=copy.deepcopy(old['nodes'][i])
            if i not in (0,1):n['children']=[];n.pop('pieces',None)
            else:
                for e in n['children']:
                    for d in e['destinations']:d['node']=mapping[d['node']]
            nodes.append(n)
        cls.source=dict(format=old['format'],roots=dict(zero=0,positive=1),cells=old['cells'],nodes=nodes)
    def target(self):
        g=copy.deepcopy(self.source);g['nodes'][0]['children']=[];return g
    def test_transferred_rule_keeps_children_unproved(self):
        g,summary,audit=transfer(self.target(),self.source,[0])
        self.assertTrue(summary['rows'][0]['accepted']);self.assertFalse(audit['failed_rules'])
        self.assertEqual(len(g['nodes']),len(self.source['nodes']))
        with self.assertRaises(ValueError):PiecewiseVerifier(g).closed()
    def test_zero_digit_rule_is_not_a_return(self):
        bad=copy.deepcopy(self.source);bad['nodes'][0]['children'][0]['suffixes']=['','']
        g,summary,audit=transfer(self.target(),bad,[0])
        self.assertFalse(summary['rows'][0]['accepted']);self.assertFalse(g['nodes'][0]['children'])
        self.assertFalse(audit['failed_rules'])
if __name__=='__main__':unittest.main()
