import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from verify_type_graph import Verifier

HERE = Path(__file__).resolve().parent


class LazySearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.temporary = tempfile.TemporaryDirectory(prefix='kf131-lazy-test-')
        cls.directory = Path(cls.temporary.name)
        cls.engine = cls.directory/'lazy'
        subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/'lazy_type_search.cpp'),
                        '-o', str(cls.engine)], check=True, capture_output=True)
        cls.output = cls.directory/'graph.json'
        subprocess.run([str(cls.engine), '2', '5', '144', '.98', '2', str(cls.output),
                        '100', '4', '2', '3', '0', '2', '200', '20000', '60'],
                       check=True, capture_output=True, timeout=70)
        cls.data = json.loads(cls.output.read_text())
        cls.progress = json.loads(Path(str(cls.output)+'.lazy.json').read_text())

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'temporary'):
            cls.temporary.cleanup()

    def test_long_suffix_geometry_uses_only_reached_cells(self):
        from itertools import product
        words = [''.join(w) for w in product('123', repeat=5)]
        legal = sum('131' not in w for w in words)
        theoretical = 2 * 144 * legal**2
        self.assertLess(self.progress['parameter_cells'], theoretical//100)
        self.assertGreater(self.progress['expanded_cells'], 0)
        self.assertTrue(all(len(s) == 5 for n in self.data['nodes'] for s in n['states']))

    def test_actual_long_suffix_rules_pass_independent_exact_audit(self):
        audit = Verifier(self.data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertTrue(audit['open_nodes'])
        self.assertEqual(audit['failed_rules'], [])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            Verifier(self.data).closed()

    def test_cell_limit_saves_open_obligation(self):
        output = self.directory/'limited.json'
        subprocess.run([str(self.engine), '1', '2', '24', '.88', '2', str(output),
                        '100', '4', '2', '3', '0', '2', '200', '1', '60'],
                       check=True, capture_output=True)
        data = json.loads(output.read_text())
        progress = json.loads(Path(str(output)+'.lazy.json').read_text())
        self.assertEqual(progress['stop'], 'parameter cell limit')
        self.assertEqual(progress['parameter_cells'], 1)
        self.assertFalse(data['closed_candidate'])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            Verifier(data).closed()

    def test_dyadic_periodic_rules_are_checked_in_the_exact_field(self):
        output = self.directory/'periodic.json'
        subprocess.run([str(self.engine), '1', '2', '24', '.88', '2', str(output),
                        '100', '4', '2', '3', '0', '2', '200', '10000', '60',
                        'dyadic', 'periodic', '9'], check=True, capture_output=True)
        data = json.loads(output.read_text())
        self.assertTrue(any('~2' in part for n in data['nodes'] for field in ('lower', 'upper')
                            for part in (n[field][0], n[field][2])))
        audit = Verifier(data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertEqual(audit['failed_rules'], [])
        self.assertFalse(data['closed_candidate'])

    def test_parallel_runner_never_accepts_false_success_flag(self):
        forged = copy.deepcopy(self.data)
        forged['closed_candidate'] = True
        source = self.directory/'forged.json'
        source.write_text(json.dumps(forged))
        fake = self.directory/'fake'
        fake.write_text(f'#!{sys.executable}\nimport shutil, sys\n'
                        f'shutil.copyfile({str(source)!r}, sys.argv[6])\n')
        fake.chmod(0o700)
        plan = self.directory/'plan.json'
        plan.write_text(json.dumps([dict(menu=1, memory=2, bins=24, base='.88', lookahead=0)]*2))
        output = self.directory/'driver'
        subprocess.run([sys.executable, str(HERE/'lazy_type_search.py'), '--engine', str(fake),
                        '--plan', str(plan), '--output-dir', str(output), '--jobs', '2'],
                       check=True, capture_output=True)
        result = json.loads((output/'summary.json').read_text())
        self.assertEqual(result['status'], 'no closed certificate obtained')
        self.assertEqual(len(result['stages']), 2)
        for stage in result['stages']:
            self.assertIn('open obligation', stage['exact_rejection'])


if __name__ == '__main__':
    unittest.main()
