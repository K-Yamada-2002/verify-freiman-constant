import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from exact import F
from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent


class AtlasSearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.temporary = tempfile.TemporaryDirectory(prefix='kf131-atlas-test-')
        directory = Path(cls.temporary.name)
        engine, output = directory/'atlas', directory/'graph.json'
        cls.engine, cls.directory = engine, directory
        subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/'atlas_type_search.cpp'),
                        '-o', str(engine)], check=True, capture_output=True)
        subprocess.run([str(engine), '1', '2', '24', '.88', '2', str(output),
                        '200', '4', '3', '3', '0', '2', '500', '10000', '60',
                        'adaptive', 'extrema', '9', '256'], check=True, capture_output=True)
        cls.data = json.loads(output.read_text())

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'temporary'):
            cls.temporary.cleanup()

    def test_adjacent_child_atoms_give_valid_uniform_local_rules(self):
        audit = ScalarVerifier(self.data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertTrue(audit['open_nodes'])
        self.assertEqual(audit['failed_rules'], [])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            ScalarVerifier(self.data).closed()

    def test_both_projections_are_insufficient_for_product_coverage(self):
        verifier = ScalarVerifier(self.data)
        hbox, interval = (F(1,4), F(3,4)), (F(0), F(1))
        diagonal = [((F(1,4),F(1,2)),(F(0),F(1,2))),
                    ((F(1,2),F(3,4)),(F(1,2),F(1)))]
        # Each projection covers its whole axis; two opposite corners are
        # nevertheless missing from the product.
        verifier.covers_ratio(hbox, [r[0] for r in diagonal])
        verifier.covers_ratio(interval, [r[1] for r in diagonal])
        with self.assertRaisesRegex(ValueError, 'parameter x scalar'):
            verifier.covers_parameter_interval(hbox, interval, diagonal)

    def test_product_cover_includes_all_closed_seams(self):
        verifier = ScalarVerifier(self.data)
        rectangles = [(h, t) for h in ((F(1,4),F(1,2)),(F(1,2),F(3,4)))
                      for t in ((F(0),F(1,2)),(F(1,2),F(1)))]
        verifier.covers_parameter_interval((F(1,4),F(3,4)),(F(0),F(1)),rectangles)
        verifier.covers_parameter_interval((F(1,2),F(1,2)),(F(0),F(1)),rectangles)

    def test_missing_scalar_strip_is_rejected_despite_ratio_coverage(self):
        data = copy.deepcopy(self.data)
        index, case = next((i, case) for i, node in enumerate(data['nodes']) if node['covered']
                           for edge in node['children'] for case in edge['cases']
                           if case['interval'][1]-case['interval'][0] > 1)
        low = case['interval'][0]
        case['destinations'] = [j for j in case['destinations']
                                if data['nodes'][j]['interval'][0] != low]
        self.assertTrue(case['destinations'])
        with self.assertRaisesRegex(ValueError, 'parameter x scalar'):
            ScalarVerifier(data).local(index)

    def test_frontier_extraction_preserves_every_retained_dependency(self):
        from extract_type_frontier import extract
        reduced = extract(self.data, 3)
        self.assertEqual(sum(n['covered'] for n in reduced['nodes']), 3)
        audit = ScalarVerifier(reduced).audit()
        self.assertEqual(len(audit['verified_rules']), 3)
        self.assertEqual(audit['failed_rules'], [])
        self.assertTrue(audit['open_nodes'])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            ScalarVerifier(reduced).closed()

    def test_failed_coarse_types_can_use_longer_suffix_boxes(self):
        output = self.directory/'refinement.json'
        subprocess.run([str(self.engine), '1', '4', '72', '.96', '2', str(output),
                        '500', '4', '2', '3', '0', '1', '1000', '10000', '60',
                        'adaptive', 'extrema', '9', '256', '128', '2', '4', '1'],
                       check=True, capture_output=True)
        data = json.loads(output.read_text())
        progress = json.loads(Path(str(output)+'.lazy.json').read_text())
        lengths = {len(word) for node in data['nodes'] for word in node['states']}
        self.assertEqual(lengths, {2, 3, 4})
        self.assertGreater(progress['deep_rejections'], 0)
        audit = ScalarVerifier(data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertEqual(audit['failed_rules'], [])

    def test_custom_root_prefixes_and_exchange_have_exact_physical_seed(self):
        output = self.directory/'custom-root.json'
        subprocess.run([str(self.engine), '1', '3', '72', '.96', '2', str(output),
                        '200', '4', '2', '3', '0', '1', '100', '10000', '60',
                        'adaptive', 'extrema', '9', '256', '128', '2', '3', '1',
                        '2222222', '222222'], check=True, capture_output=True)
        data = json.loads(output.read_text())
        self.assertEqual(data['root_prefixes'], ['222222', '2222222'])
        self.assertEqual(data['nodes'][0]['parity'], -1)
        audit = ScalarVerifier(data).audit()
        self.assertEqual(audit['failed_rules'], [])
        self.assertTrue(audit['root_interval'])


if __name__ == '__main__':
    unittest.main()
