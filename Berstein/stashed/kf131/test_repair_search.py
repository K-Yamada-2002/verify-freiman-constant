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


class RepairSearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if compiler is None:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.temporary = tempfile.TemporaryDirectory(prefix='kf131-repair-test-')
        cls.directory = Path(cls.temporary.name)
        cls.engine = cls.directory/'search'
        cls.game = cls.directory/'game'
        cls.outer = cls.directory/'outer'
        for source, binary in [('repair_type_search.cpp', cls.engine),
                               ('test_finite_cover_game.cpp', cls.game),
                               ('test_outer_type_filter.cpp', cls.outer)]:
            subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/source),
                            '-o', str(binary)], check=True, capture_output=True)
        output = cls.directory/'graph.json'
        subprocess.run([str(cls.engine), '1', '1', '8', '.7', '2', '1',
                        str(output), '50', '4'], check=True, capture_output=True)
        cls.data = json.loads(output.read_text())
        cls.search = json.loads(Path(str(output)+'.search.json').read_text())

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'temporary'):
            cls.temporary.cleanup()

    def test_fixed_point_and_backtracking_cases(self):
        subprocess.run([str(self.game)], check=True, capture_output=True)

    def test_outer_filter_retains_witnesses_and_detects_finite_gaps(self):
        subprocess.run([str(self.outer)], check=True, capture_output=True)

    def test_real_geometry_frontier_is_open_and_local_rules_are_exact(self):
        self.assertTrue(self.search['limit_reached'])
        self.assertGreater(self.search['parent_replans'], 0)
        self.assertFalse(self.data['closed_candidate'])
        audit = Verifier(self.data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertTrue(audit['open_nodes'])
        self.assertEqual(audit['failed_rules'], [])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            Verifier(self.data).closed()

    def test_runner_rejects_a_false_discovery_success_flag(self):
        forged = copy.deepcopy(self.data)
        forged['closed_candidate'] = True
        source = self.directory/'forged.json'
        source.write_text(json.dumps(forged))
        fake = self.directory/'fake_engine'
        fake.write_text(f'#!{sys.executable}\n'
                        'import shutil, sys\n'
                        f'shutil.copyfile({str(source)!r}, sys.argv[7])\n')
        fake.chmod(0o700)
        output = self.directory/'driver'
        subprocess.run([sys.executable, str(HERE/'repair_type_search.py'),
                        '--engine', str(fake), '--stages', '1',
                        '--output-dir', str(output)], check=True, capture_output=True)
        report = json.loads((output/'summary.json').read_text())
        self.assertEqual(report['status'], 'no closed certificate obtained')
        self.assertIn('open obligation', report['stages'][0]['exact_rejection'])
        self.assertFalse((output/'proof_audit.json').exists())

    def test_time_limit_keeps_only_a_fresh_checkpoint(self):
        source = self.directory/'open.json'
        source.write_text(json.dumps(self.data))
        for fresh in (False, True):
            fake = self.directory/f'timed_engine_{fresh}'
            fake.write_text(f'#!{sys.executable}\n'
                            'import shutil, sys, time\n'
                            + (f'shutil.copyfile({str(source)!r}, sys.argv[7])\n'
                               if fresh else '') + 'time.sleep(10)\n')
            fake.chmod(0o700)
            output = self.directory/f'timed_{fresh}'
            output.mkdir()
            # A stale output is not evidence about this invocation.
            (output/'stage_01.json').write_text(json.dumps(self.data))
            subprocess.run([sys.executable, str(HERE/'repair_type_search.py'),
                            '--engine', str(fake), '--stages', '1',
                            '--stage-seconds', '.5', '--output-dir', str(output)],
                           check=True, capture_output=True)
            report = json.loads((output/'summary.json').read_text())
            self.assertIn('time limit', report['stages'][0]['stop'])
            self.assertEqual('parameterized_types' in report['stages'][0], fresh)
            self.assertEqual(report['status'], 'no closed certificate obtained')


if __name__ == '__main__':
    unittest.main()
