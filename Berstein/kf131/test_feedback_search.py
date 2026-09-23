import json
import gzip
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from extract_type_frontier import extract
from feedback_resume import write_frontier
from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent


class FeedbackChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if not compiler:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.tmp = tempfile.TemporaryDirectory(prefix='kf131-feedback-test-')
        cls.directory = Path(cls.tmp.name)
        cls.engine = cls.directory/'feedback'
        cls.registry_test = cls.directory/'registry'
        cls.sieve_test = cls.directory/'sieve'
        for source, target in [('feedback_type_search.cpp', cls.engine),
                               ('test_feedback_registry.cpp', cls.registry_test),
                               ('test_point_sieve.cpp', cls.sieve_test)]:
            subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/source), '-o', str(target)],
                           check=True, capture_output=True)
        output = cls.directory/'graph.json'
        subprocess.run([str(cls.engine), '1', '3', '72', '.96', '2', str(output),
                        '1200', '4', '2', '3', '0', '4', '2000', '10000', '60',
                        'adaptive', 'extrema', '9', '256', '128', '2', '4', '1',
                        '112222', '122222', '16', '1', '20', '1', '1', '1000', '64', '3', '1'],
                       check=True, capture_output=True)
        cls.data = json.loads(output.read_text())
        cls.source = output
        cls.history = json.loads(Path(str(output)+'.feedback.json').read_text())

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'tmp'):
            cls.tmp.cleanup()

    def test_complete_repair_is_registered_atomically(self):
        subprocess.run([str(self.registry_test)], check=True, capture_output=True)

    def test_actual_feedback_rules_pass_exact_audit_without_false_closure(self):
        data = extract(self.data, 32)
        audit = ScalarVerifier(data).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertFalse(audit['failed_rules'])
        self.assertTrue(audit['open_nodes'])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            ScalarVerifier(data).closed()

    def test_failed_finite_dictionary_drives_new_types(self):
        history = self.history
        self.assertGreater(len(history['rounds']), 2)
        self.assertGreater(history['new_types_from_repairs'], 0)
        self.assertGreater(history['repairs_avoiding_failed'], 0)
        self.assertTrue(any(r['registered_after'] > r['registered_before']
                            and r['installed_repairs'] > 0 for r in history['rounds']))
        self.assertFalse(self.data['closed_candidate'])

    def test_fast_point_sieve_and_actual_seed_realization(self):
        result = subprocess.run([str(self.sieve_test)], check=True, capture_output=True, text=True)
        cases = json.loads(result.stdout)
        self.assertGreaterEqual(len(cases), 40)
        for case in cases:
            data = dict(schema='kf131-scalar-atlas-v1',settings=dict(base='.96',bins=72,grid=256),
                        root_prefixes=case['root_prefixes'],roots=[0],nodes=[dict(id=0,
                        states=case['states'],parity=case['parity'],ratio_bin=case['ratio_bin'],
                        interval=[0,1],covered=False,children=[])])
            ScalarVerifier(data).seed()

    def test_existing_components_are_trimmed_to_needed_preimages(self):
        self.assertTrue(self.history['trim_known_ranges'])
        self.assertGreater(self.history['known_range_trims'], 0)
        self.assertGreater(self.history['known_range_atoms_removed'], 0)
        # Independent number-field replay checks the actual trimmed rules,
        # not just the floating-point counters or the discovery success flag.
        data = extract(self.data, 64)
        audit = ScalarVerifier(data).audit()
        self.assertGreater(len(audit['verified_rules']), 0)
        self.assertFalse(audit['failed_rules'])

    def test_saved_frontier_can_continue_with_all_dependencies(self):
        cfg = dict(base='.96', bins=72, memory=3, scalar_grid=256,
                   max_types=2500, minimum_memory=2, max_step=2)
        imported = self.directory/'resume.txt'
        metadata = write_frontier(self.source, imported, cfg)
        compressed = self.directory/'resume.json.gz'
        compressed.write_bytes(gzip.compress(self.source.read_bytes(), mtime=0))
        second = self.directory/'compressed-resume.txt'
        compressed_metadata = write_frontier(compressed, second, cfg)
        self.assertEqual(imported.read_bytes(), second.read_bytes())
        self.assertEqual(metadata['decoded_graph_sha256'], compressed_metadata['decoded_graph_sha256'])
        output = self.directory/'resumed.json'
        subprocess.run([str(self.engine), '1', '3', '72', '.96', '2', str(output),
                        '2500', '4', '2', '3', '0', '4', '2000', '10000', '8',
                        'adaptive', 'extrema', '9', '256', '128', '2', '4', '1',
                        cfg['root_left'], cfg['root_right'], '16', '1', '20', '1', '1',
                        '1000', '64', '3', '1', '0', '5', '1', str(imported)],
                       check=True, capture_output=True)
        history = json.loads(Path(str(output)+'.feedback.json').read_text())
        self.assertEqual(history['imported_types'], metadata['imported_nodes'])
        self.assertEqual(history['imported_rules'], metadata['imported_rules'])
        data = extract(json.loads(output.read_text()), 32)
        audit = ScalarVerifier(data).audit()
        self.assertFalse(audit['failed_rules'])
        self.assertTrue(audit['verified_rules'])
        self.assertTrue(audit['open_nodes'])

    def test_frontier_import_refuses_different_geometry(self):
        cfg = dict(base='.96', bins=72, memory=3, scalar_grid=512,
                   max_types=2500, minimum_memory=2, max_step=2)
        with self.assertRaisesRegex(ValueError, 'resume geometry differs: grid'):
            write_frontier(self.source, self.directory/'bad.txt', cfg)


if __name__ == '__main__':
    unittest.main()
