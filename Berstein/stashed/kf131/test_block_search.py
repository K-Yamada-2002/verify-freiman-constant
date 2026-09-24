import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from extract_type_frontier import extract
from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent


class BlockSearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.temporary = tempfile.TemporaryDirectory(prefix='kf131-block-test-')
        cls.directory = Path(cls.temporary.name)
        cls.engine = cls.directory/'block'
        subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/'block_type_search.cpp'),
                        '-o', str(cls.engine)], check=True, capture_output=True)
        output = cls.directory/'graph.json'
        subprocess.run([str(cls.engine), '1', '3', '72', '.96', '2', str(output),
                        '15000', '4', '2', '3', '0', '3', '10000', '40000', '60',
                        'adaptive', 'extrema', '9', '256', '128', '2', '4', '1',
                        '112222', '122222', '32', '1', '30', '0'],
                       check=True, capture_output=True)
        cls.data = json.loads(output.read_text())
        cls.progress = json.loads(Path(str(output)+'.lazy.json').read_text())

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'temporary'):
            cls.temporary.cleanup()

    def test_compressed_blocks_keep_every_induction_obligation(self):
        data = extract(self.data, 48)
        audit = ScalarVerifier(data).audit()
        self.assertEqual(len(audit['verified_rules']), 48)
        self.assertEqual(audit['failed_rules'], [])
        self.assertTrue(audit['open_nodes'])
        self.assertTrue(any(n['interval'][1]-n['interval'][0] > 1 for n in data['nodes']))
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            ScalarVerifier(data).closed()

    def test_piecewise_successor_maps_pass_independent_exact_checks(self):
        indices = [i for i, node in enumerate(self.data['nodes']) if len(node['children']) > 1]
        self.assertTrue(indices)
        checker = ScalarVerifier(self.data)
        for index in indices[:12]:
            checker.local(index)

    def test_missing_branch_is_not_hidden_by_interval_compression(self):
        data = copy.deepcopy(self.data)
        index = next(i for i, n in enumerate(data['nodes']) if len(n['children']) > 1)
        data['nodes'][index]['children'][0]['cases'][0]['destinations'] = []
        with self.assertRaisesRegex(ValueError, 'empty destination'):
            ScalarVerifier(data).local(index)

    def test_finite_dictionary_probe_is_separate_from_open_discovery_graph(self):
        self.assertGreater(self.progress['probe_steps'], 0)
        self.assertGreater(self.progress['probe_rejections'], 0)
        self.assertGreater(self.progress['known_cover_successes'], 0)
        self.assertFalse(self.progress['probe_closed'])
        self.assertFalse(self.data['closed_candidate'])
        self.assertGreater(self.progress['represented_distinct_atoms'], len(self.data['nodes']))

    def test_shared_dependency_scheduler_retains_open_frontier(self):
        output = self.directory/'shared.json'
        subprocess.run([str(self.engine), '1', '3', '72', '.96', '2', str(output),
                        '300', '4', '2', '3', '0', '1', '1000', '10000', '30',
                        'adaptive', 'extrema', '9', '256', '128', '2', '4', '1',
                        '112222', '122222', '16', '1', '20', '2'],
                       check=True, capture_output=True)
        data = json.loads(output.read_text())
        audit = ScalarVerifier(data).audit()
        self.assertEqual(audit['failed_rules'], [])
        self.assertTrue(audit['open_nodes'])
        self.assertFalse(data['closed_candidate'])

    def test_one_grid_atom_can_need_two_different_successors(self):
        output = self.directory/'subgrid.json'
        subprocess.run([str(self.engine), '1', '3', '72', '.96', '2', str(output),
                        '5000', '4', '2', '3', '0', '2', '5000', '20000', '60',
                        'adaptive', 'extrema', '9', '256', '128', '2', '4', '1',
                        '112222', '122222', '16', '1', '30', '0', '2'],
                       check=True, capture_output=True)
        data = json.loads(output.read_text())
        checker = ScalarVerifier(data)
        witnesses = []
        for index, node in enumerate(data['nodes']):
            if node['interval'][1]-node['interval'][0] != 1 or len(node['children']) < 2:
                continue
            a, b = checker.interval(node['interval'])
            cores = [checker.scalar_child(index, edge)[0] for edge in node['children']]
            if all(not (lo <= a and b <= hi) for lo, hi in cores):
                checker.local(index)
                witnesses.append(index)
        self.assertTrue(witnesses, 'expected a valid cover with no individually sufficient successor')


if __name__ == '__main__':
    unittest.main()
