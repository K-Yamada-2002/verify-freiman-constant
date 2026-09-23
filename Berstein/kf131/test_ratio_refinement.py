import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from exact import F
from extract_type_frontier import extract
from feedback_resume import write_frontier
from verify_scalar_graph import ScalarVerifier

HERE = Path(__file__).resolve().parent


class RatioRefinementChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = extract(json.loads((HERE/'feedback_block_frontier.json').read_text()), 1)
        cls.split = copy.deepcopy(cls.old)
        nodes = [copy.deepcopy(cls.old['nodes'][0])]
        ids = {0: [0]}
        for n in cls.old['nodes'][1:]:
            ids[n['id']] = []
            for part in (0, 1):
                child = copy.deepcopy(n)
                child.update(id=len(nodes), covered=False, children=[], ratio_refinement=[1,part])
                ids[n['id']].append(len(nodes)); nodes.append(child)
        for edge in nodes[0]['children']:
            for case in edge['cases']:
                case['destinations'] = [k for j in case['destinations'] for k in ids[j]]
        cls.split.update(nodes=nodes, open_nodes=len(nodes)-1, closed_candidate=False)

    def test_exact_subboxes_partition_the_original_ratio_box(self):
        old = ScalarVerifier(self.old)
        v = ScalarVerifier(self.split)
        for j in range(1, len(self.old['nodes'])):
            original = old.box(j)[2]
            a, b = v.box(2*j-1)[2], v.box(2*j)[2]
            self.assertEqual((a[0],a[1],b[1]),
                             (original[0],sum(original)/2,original[1]))
            self.assertEqual(a[1], b[0])

    def test_whole_local_cover_remains_exact_after_parameter_subdivision(self):
        v = ScalarVerifier(self.split)
        v.local(0)
        self.assertEqual(v.seed(), ScalarVerifier(self.old).seed())
        with self.assertRaisesRegex(ValueError, 'open obligation'):
            v.closed()

    def test_missing_parameter_half_cannot_be_hidden(self):
        data = copy.deepcopy(self.split)
        for edge in data['nodes'][0]['children']:
            for case in edge['cases']:
                case['destinations'] = [j for j in case['destinations'] if
                                        data['nodes'][j].get('ratio_refinement',[0,0])[1] == 0]
        with self.assertRaisesRegex(ValueError, 'parameter boxes|cover the image|parameter x scalar'):
            ScalarVerifier(data).local(0)

    def test_refinement_is_validated_and_included_in_mathematical_hash(self):
        data = copy.deepcopy(self.old)
        original_hash = ScalarVerifier(data).proof_hash()
        data['nodes'][1]['ratio_refinement'] = [1,0]
        self.assertNotEqual(original_hash, ScalarVerifier(data).proof_hash())
        for invalid in ([1,2],[-1,0],[True,0],[17,0],[2], '1,0'):
            data['nodes'][1]['ratio_refinement'] = invalid
            with self.assertRaisesRegex(ValueError, 'invalid ratio refinement'):
                ScalarVerifier(data).box(1)

    def test_native_refinement_keeps_exactly_the_required_halves(self):
        compiler = shutil.which('clang++') or shutil.which('g++')
        if not compiler: self.skipTest('C++ compiler unavailable')
        with tempfile.TemporaryDirectory(prefix='kf131-ratio-test-') as tmp:
            engine = Path(tmp)/'test'
            subprocess.run([compiler,'-std=c++17','-O1',str(HERE/'test_ratio_refinement.cpp'),
                            '-o',str(engine)],check=True,capture_output=True)
            subprocess.run([str(engine)],check=True,capture_output=True)

    def test_resume_refuses_a_depth_that_discards_required_subboxes(self):
        with tempfile.TemporaryDirectory(prefix='kf131-ratio-depth-') as tmp:
            source=Path(tmp)/'input.json'
            source.write_text(json.dumps(self.split))
            cfg=dict(base='.996',bins=512,memory=5,minimum_memory=3,
                     scalar_grid=2048,max_step=3,max_types=4000,ratio_depth=0)
            with self.assertRaisesRegex(ValueError,'refinement exceeds ratio depth'):
                write_frontier(source,Path(tmp)/'import.txt',cfg)

    def test_native_resume_preserves_refined_types_and_exact_local_rules(self):
        compiler=shutil.which('clang++') or shutil.which('g++')
        if not compiler:self.skipTest('C++ compiler unavailable')
        with tempfile.TemporaryDirectory(prefix='kf131-ratio-resume-') as tmp:
            tmp=Path(tmp);engine=tmp/'feedback';source=tmp/'input.json'
            source.write_text(json.dumps(self.split))
            cfg=dict(base='.996',bins=512,memory=5,minimum_memory=3,
                     scalar_grid=2048,max_step=3,max_types=4000,ratio_depth=1)
            imported=tmp/'import.txt'
            metadata=write_frontier(source,imported,cfg)
            subprocess.run([compiler,'-std=c++17','-O1',str(HERE/'feedback_type_search.cpp'),
                            '-o',str(engine)],check=True,capture_output=True)
            output=tmp/'output.json'
            subprocess.run([str(engine),'1','5','512','.996','3',str(output),
                            '4000','4','3','3','0','2','1000','10000','3',
                            'adaptive','extrema','9','2048','128','3','4','1',
                            cfg['root_left'],cfg['root_right'],'4','1','20','1','2',
                            '1000','64','1','1','0','5','1',str(imported),'1'],
                           check=True,capture_output=True)
            history=json.loads(Path(str(output)+'.feedback.json').read_text())
            self.assertEqual(history['imported_types'],metadata['imported_nodes'])
            self.assertGreater(history['refined_ratio_bins'],0)
            data=extract(json.loads(output.read_text()),8)
            audit=ScalarVerifier(data).audit()
            self.assertTrue(audit['verified_rules'])
            self.assertFalse(audit['failed_rules'])
            with self.assertRaisesRegex(ValueError,'open obligation'):
                ScalarVerifier(data).closed()


if __name__ == '__main__': unittest.main()
