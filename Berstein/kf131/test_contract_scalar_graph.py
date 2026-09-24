import copy
import json
from pathlib import Path
import unittest

from contract_scalar_graph import attach_partial,contract
from verify_scalar_graph import ScalarVerifier


class ContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder = Path(__file__).parent
        cls.base = json.loads((folder/'refined_seed_run_20260924/batch_001.patch.json').read_text())
        cls.base['root_prefixes'] = json.loads((folder/'closure_revised_seed_20260924.json').read_text())['prefixes']
        cls.patch = json.loads((folder/'refined_seed_run_20260924/batch_002.patch.json').read_text())

    def narrower_patch(self):
        patch = copy.deepcopy(self.patch)
        patch['roots'] = patch['roots'][:1]
        n = patch['nodes'][patch['roots'][0]]
        a,b = n['interval']
        n['interval'] = [a,(a+b)//2]
        return patch

    def test_child_restriction_propagates_to_physical_root(self):
        attached = attach_partial(self.base,self.narrower_patch())
        with self.assertRaises(ValueError):
            ScalarVerifier(attached).local(0)
        result,report = contract(attached)
        a,b = self.base['nodes'][0]['interval']
        c,d = result['nodes'][0]['interval']
        self.assertTrue(a <= c < d <= b)
        self.assertLess(d-c,b-a)
        self.assertNotEqual(report['physical_interval'],ScalarVerifier(self.base).seed())
        for n in result['nodes']:
            if n['covered']:
                ScalarVerifier(result).local(n['id'])
        with self.assertRaisesRegex(ValueError,'open obligation'):
            ScalarVerifier(result).closed()

    def test_patch_may_not_expand_a_source_interval(self):
        patch = self.narrower_patch()
        patch['nodes'][patch['roots'][0]]['interval'][0] -= 1
        with self.assertRaisesRegex(ValueError,'does not restrict'):
            attach_partial(self.base,patch)

    def test_empty_parent_core_is_not_a_proof(self):
        data = copy.deepcopy(self.base)
        data['nodes'][1]['interval'] = [600000000,600000001]
        with self.assertRaisesRegex(ValueError,'no surviving conditional core'):
            contract(data)

    def test_unchanged_single_rule_needs_no_root_restriction(self):
        result,_ = contract(self.base)
        self.assertEqual(result['nodes'][0]['interval'],self.base['nodes'][0]['interval'])

    def test_partial_rule_does_not_certify_original_interval(self):
        folder = Path(__file__).parent
        patch = json.loads((folder/'refined_partial_patch_20260924.json').read_text())
        report = json.loads((folder/'refined_partial_report_20260924.json').read_text())
        partial = report['partial_parents'][0]
        j = next(j for j in patch['roots'] if patch['nodes'][j]['source_node'] == partial['parent'])
        ScalarVerifier(patch).local(j)
        patch['nodes'][j]['interval'] = partial['original']
        with self.assertRaisesRegex(ValueError,'upper end is not covered'):
            ScalarVerifier(patch).local(j)


if __name__ == '__main__':
    unittest.main()
