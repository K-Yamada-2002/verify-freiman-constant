"""Learning changes proposal ranking, while exact arithmetic checks acceptance."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from feedback_resume import write_frontier
from extract_type_frontier import extract
from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent


class LearningChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if not compiler:
            raise unittest.SkipTest('C++17 compiler unavailable')
        cls.tmp = tempfile.TemporaryDirectory(prefix='kf131-learning-tests-')
        cls.directory = Path(cls.tmp.name)
        for name in ('feedback_type_search', 'test_weighted_cover',
                     'test_feedback_learning', 'test_alternative_cover_game'):
            subprocess.run([compiler, '-O1', '-std=c++17', str(HERE/(name+'.cpp')),
                            '-o', str(cls.directory/name)], check=True, capture_output=True)
        cls.source = cls.directory/'first.json'
        cls.run_search(cls.source, 4000, 18)
        cls.catalog_path = Path(str(cls.source)+'.catalog.json')
        cls.catalog = json.loads(cls.catalog_path.read_text())
        cls.history = json.loads(Path(str(cls.source)+'.feedback.json').read_text())

    @classmethod
    def run_search(cls, output, limit, seconds, resume='-', learning='-', memory=3):
        command = [str(cls.directory/'feedback_type_search'), '1', str(memory), '72', '.96',
                   '2', str(output), str(limit), '4', '2', '3', '0', '4', '2000',
                   '10000', str(seconds), 'adaptive', 'extrema', '9', '256', '128',
                   '2', '4', '1', '112222', '122222', '16', '1', '20', '1', '1',
                   '1000', '64', '3', '1', '0', '5', '1', str(resume), '0', '1',
                   '1', '0', '4', str(learning), '1']
        subprocess.run(command, check=True, capture_output=True)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_interval_minimum_matches_exhaustive_search(self):
        subprocess.run([str(self.directory/'test_weighted_cover')], check=True, capture_output=True)

    def test_failure_costs_and_history_roundtrip(self):
        subprocess.run([str(self.directory/'test_feedback_learning'),
                        str(self.directory/'toy.txt')], check=True, capture_output=True)

    def test_alternative_fixed_point_matches_all_subsets(self):
        subprocess.run([str(self.directory/'test_alternative_cover_game')], check=True, capture_output=True)

    def test_selected_and_retained_rules_pass_exact_arithmetic(self):
        self.assertGreater(self.history['weighted_slice_queries'], 0)
        self.assertGreater(self.history['retained_alternative_rules'], 0)
        self.assertGreater(self.history['retained_rule_reuses'], 0)
        self.assertGreater(self.history['alternative_fixed_point_checks'], 0)
        data = json.loads(self.source.read_text())
        audit = ScalarVerifier(extract(data, 24)).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertFalse(audit['failed_rules'])
        # Replay distinct retained alternatives, including discarded choices.
        sample = copy.deepcopy(self.catalog)
        sample.pop('alternative_rules')
        for node in sample['nodes']:
            node.update(covered=False, children=[])
        chosen = {}
        for alternative in self.catalog['alternative_rules']:
            chosen[alternative['parent']] = alternative['children']
            if len(chosen) >= 24: break
        for parent, edges in chosen.items():
            sample['nodes'][parent].update(covered=True, children=edges)
        sample['open_nodes'] = len(sample['nodes'])-len(chosen)
        sample['closed_candidate'] = False
        replay = ScalarVerifier(sample).audit()
        self.assertEqual(len(replay['verified_rules']),len(chosen))
        self.assertFalse(replay['failed_rules'])
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            ScalarVerifier(sample).closed()

    def test_full_dictionary_alternatives_and_learning_resume_together(self):
        cfg = dict(base='.96', bins=72, memory=3, scalar_grid=256,
                   max_types=6000, minimum_memory=2, max_step=2)
        native = self.directory/'resume.txt'
        metadata = write_frontier(self.catalog_path,native,cfg)
        self.assertTrue(native.read_text().startswith('kf131-frontier-v3'))
        self.assertEqual(metadata['imported_alternatives'],len(self.catalog['alternative_rules']))
        output = self.directory/'resumed.json'
        self.run_search(output,6000,8,native,Path(str(self.source)+'.learning.txt'))
        history = json.loads(Path(str(output)+'.feedback.json').read_text())
        self.assertEqual(history['imported_alternatives'],metadata['imported_alternatives'])
        self.assertEqual(history['imported_learning_keys'],self.history['distinct_conditional_failures'])
        self.assertGreaterEqual(history['retained_alternative_rules'],metadata['imported_alternatives'])
        self.assertEqual(history['imported_types'],len(self.catalog['nodes']))
        audit = ScalarVerifier(extract(json.loads(output.read_text()),24)).audit()
        self.assertFalse(audit['failed_rules'])

    def test_resume_can_raise_suffix_memory_without_changing_old_boxes(self):
        cfg = dict(base='.96',bins=72,memory=5,scalar_grid=256,
                   max_types=6000,minimum_memory=2,max_step=2)
        native = self.directory/'longer-memory.txt'
        write_frontier(self.catalog_path,native,cfg)
        output = self.directory/'longer-memory.json'
        self.run_search(output,6000,8,native,memory=5)
        history = json.loads(Path(str(output)+'.feedback.json').read_text())
        self.assertEqual(history['imported_types'],len(self.catalog['nodes']))
        audit = ScalarVerifier(extract(json.loads(output.read_text()),24)).audit()
        self.assertFalse(audit['failed_rules'])

    def test_resume_rejects_incomplete_alternative(self):
        data = copy.deepcopy(self.catalog)
        data['alternative_rules'][0]['children'][0]['cases'][0]['destinations'] = []
        source = self.directory/'broken.json'
        source.write_text(json.dumps(data))
        cfg = dict(base='.96',bins=72,memory=3,scalar_grid=256,
                   max_types=6000,minimum_memory=2,max_step=2)
        with self.assertRaisesRegex(ValueError,'missing dependencies'):
            write_frontier(source,self.directory/'broken.txt',cfg)


if __name__ == '__main__':
    unittest.main()
