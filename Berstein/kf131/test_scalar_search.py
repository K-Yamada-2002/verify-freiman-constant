import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent


class ScalarSearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.temporary = tempfile.TemporaryDirectory(prefix='kf131-scalar-test-')
        directory = Path(cls.temporary.name)
        engine, output = directory/'scalar', directory/'graph.json'
        subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/'scalar_type_search.cpp'),
                        '-o', str(engine)], check=True, capture_output=True)
        subprocess.run([str(engine), '1', '8', '.7', '2', '128', '1', str(output)],
                       check=True, capture_output=True)
        cls.data = json.loads(output.read_text())

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'temporary'):
            cls.temporary.cleanup()

    def test_local_rules_pass_but_frontier_prevents_closure(self):
        audit = ScalarVerifier(self.data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertTrue(audit['open_nodes'])
        self.assertEqual(audit['failed_rules'], [])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            ScalarVerifier(self.data).closed()

    def test_missing_parameter_destination_is_rejected(self):
        data = copy.deepcopy(self.data)
        data['nodes'][0]['children'][0]['cases'][0]['destinations'].clear()
        with self.assertRaisesRegex(ValueError, 'empty destination'):
            ScalarVerifier(data).local(0)

    def test_oversized_child_interval_is_rejected(self):
        data = copy.deepcopy(self.data)
        data['nodes'][0]['children'][0]['cases'][0]['interval'][1] = 1000000
        with self.assertRaisesRegex(ValueError, 'escapes destination'):
            ScalarVerifier(data).local(0)

    def test_nonshrinking_rule_is_rejected(self):
        data = copy.deepcopy(self.data)
        data['nodes'][0]['children'][0]['suffixes'] = ['', '']
        with self.assertRaisesRegex(ValueError, 'non-shrinking'):
            ScalarVerifier(data).local(0)

    def test_grid_is_part_of_the_mathematical_hash(self):
        data = copy.deepcopy(self.data)
        data['settings']['grid'] *= 2
        self.assertNotEqual(ScalarVerifier(data).proof_hash(), ScalarVerifier(self.data).proof_hash())


if __name__ == '__main__':
    unittest.main()
