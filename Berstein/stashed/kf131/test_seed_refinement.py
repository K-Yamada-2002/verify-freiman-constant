import json
from pathlib import Path
import unittest

from exact import F
from refine_scalar_seed import refine
from repair_gap_intervals import gap_envelope
from verify_scalar_graph import ScalarVerifier
from continue_gap_closure import backtrack_refuted_children


class SeedRefinementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder = Path(__file__).parent
        cls.graph = json.loads((folder/'closure_revised_patch_20260924.json').read_text())
        cls.seed = json.loads((folder/'closure_revised_seed_20260924.json').read_text())
        cls.cert = json.loads((folder/'closure_root_obstructions_20260924.json').read_text())['obstructions'][0]

    def test_refinement_preserves_physical_interval_but_not_old_rules(self):
        data,report = refine(self.graph,self.seed['prefixes'],8,6)
        self.assertEqual(report['physical_interval'],self.seed['physical_interval'])
        self.assertEqual(len(data['nodes']),1)
        self.assertFalse(data['nodes'][0]['covered'])
        self.assertEqual(data['nodes'][0]['children'],[])
        with self.assertRaisesRegex(ValueError,'open obligation'):
            ScalarVerifier(data).closed()

    def test_larger_shape_box_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'not a refinement'):
            refine(self.graph,self.seed['prefixes'],2,6)

    def test_gap_envelope_contracts_on_subbox(self):
        v = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',settings=self.cert['settings'],nodes=[self.cert['type']]))
        boxes = v.box(0)
        grid = 1024000000
        outer = gap_envelope(self.cert,grid)
        innerbox = tuple(((3*a+b)/4,(a+3*b)/4) for a,b in boxes)
        inner = gap_envelope(self.cert,grid,innerbox)
        self.assertLessEqual(outer[0],inner[0])
        self.assertLessEqual(inner[1],outer[1])
        self.assertLess(inner[1]-inner[0],outer[1]-outer[0])

    def test_point_envelope_contains_exact_excluded_point(self):
        params = tuple(map(F,self.cert['parameters']))
        grid = 1024000000
        a,b = gap_envelope(self.cert,grid,tuple((x,x) for x in params))
        self.assertLess(F(a,grid),F(self.cert['target']))
        self.assertLess(F(self.cert['target']),F(b,grid))

    def test_false_child_reopens_parent_without_refuting_it(self):
        folder = Path(__file__).parent
        certs = json.loads((folder/'closure_revised_all_audit_20260924.json').read_text())['obstructions']
        graph,retry,bad = backtrack_refuted_children(self.graph,certs)
        self.assertEqual(bad,[1])
        self.assertEqual(len(retry),1)
        self.assertEqual(len(graph['nodes']),1)
        self.assertFalse(graph['nodes'][0]['covered'])
        self.assertEqual(graph['nodes'][0]['interval'],self.graph['nodes'][0]['interval'])

    def test_refuted_root_requires_a_changed_root(self):
        graph = dict(self.graph,roots=[1])
        folder = Path(__file__).parent
        certs = json.loads((folder/'closure_revised_all_audit_20260924.json').read_text())['obstructions']
        with self.assertRaisesRegex(ValueError,'fixed root is refuted'):
            backtrack_refuted_children(graph,certs)


if __name__ == '__main__':
    unittest.main()
