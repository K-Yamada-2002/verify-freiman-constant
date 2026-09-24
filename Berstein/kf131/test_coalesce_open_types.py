import copy
import json
from pathlib import Path
import unittest

from coalesce_open_types import coalesce
from verify_scalar_graph import ScalarVerifier


class CoalesceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((Path(__file__).parent/'refined_seed_run_20260924/batch_001.patch.json').read_text())

    def test_dyadic_siblings_merge_without_proving_child(self):
        result,report = coalesce(self.data)
        self.assertEqual(len(result['nodes']),2)
        self.assertEqual(result['nodes'][1]['ratio_refinement'],[5,31])
        self.assertFalse(result['nodes'][1]['covered'])
        self.assertEqual(result['nodes'][0]['interval'],self.data['nodes'][0]['interval'])
        self.assertTrue(ScalarVerifier(result).local(0)['dependencies'])
        with self.assertRaisesRegex(ValueError,'open obligation'):
            ScalarVerifier(result).closed()

    def with_duplicate(self,interval):
        data = copy.deepcopy(self.data)
        n = copy.deepcopy(data['nodes'][1])
        n.update(id=3,interval=interval)
        data['nodes'].append(n)
        data['nodes'][0]['children'][0]['cases'][0]['destinations'].append(3)
        return data

    def test_scalar_overlap_merges_to_exact_union(self):
        a,b = self.data['nodes'][1]['interval']
        result,report = coalesce(self.with_duplicate([a+1,b+1]))
        self.assertEqual(len(result['nodes']),3)
        self.assertIn([a,b+1],[n['interval'] for n in result['nodes']])
        self.assertEqual(report['merges'][0]['kind'],'scalar union')

    def test_scalar_gap_is_not_filled_by_merging(self):
        a,b = self.data['nodes'][1]['interval']
        result,_ = coalesce(self.with_duplicate([a-20,a-10]))
        self.assertEqual(len(result['nodes']),3)
        self.assertIn([a-20,a-10],[n['interval'] for n in result['nodes']])
        self.assertNotIn([a-20,b],[n['interval'] for n in result['nodes']])

    def test_coalescing_is_idempotent(self):
        result,_ = coalesce(self.data)
        again,report = coalesce(result)
        self.assertEqual(result,again)
        self.assertEqual(report['merges'],[])


if __name__ == '__main__':
    unittest.main()
