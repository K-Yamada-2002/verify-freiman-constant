import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from feedback_resume import write_frontier
from audit_alternative_bank import sample, supported
from verify_scalar_graph import ScalarVerifier

HERE=Path(__file__).resolve().parent


class GlobalSearchChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler=shutil.which('clang++') or shutil.which('g++')
        if not compiler: raise unittest.SkipTest('C++17 compiler unavailable')
        cls.tmp=tempfile.TemporaryDirectory(prefix='kf131-global-test-')
        cls.directory=Path(cls.tmp.name)
        for source,name in [('feedback_type_search.cpp','engine'),('test_global_frontier.cpp','frontier')]:
            subprocess.run([compiler,'-O1','-std=c++17',str(HERE/source),'-o',str(cls.directory/name)],check=True,capture_output=True)
        fixture=json.loads((HERE/'ratio_filtered_frontier.json').read_text())
        cls.cfg=dict(base='.996',bins=512,memory=5,scalar_grid=fixture['settings']['grid'],max_types=6000,
                     minimum_memory=3,max_step=3,ratio_depth=3)
        native=cls.directory/'start.txt'
        write_frontier(HERE/'ratio_filtered_frontier.json',native,cls.cfg)
        cls.output=cls.directory/'global.json'
        cls.run_native(cls.output,native,12)
        cls.stats=json.loads(Path(str(cls.output)+'.feedback.json').read_text())
        cls.data=json.loads(Path(str(cls.output)+'.catalog.json').read_text())

    @classmethod
    def run_native(cls,output,resume,seconds,history='-'):
        cmd=[str(cls.directory/'engine'),'1','5','512','.996','3',str(output),
             '6000','8','3','3','0','32','10000','30000',str(seconds),
             'adaptive','extrema','9',str(cls.cfg['scalar_grid']),'128','3','4','1',
             cls.cfg['root_left'],cls.cfg['root_right'],'1','1','20','1','2',
             '20000','2048','3','1','0','5','1',str(resume),'3','1','1','0',
             '4','-','1','1','4','64',str(history)]
        subprocess.run(cmd,check=True,capture_output=True,timeout=seconds+30)

    @classmethod
    def tearDownClass(cls): cls.tmp.cleanup()

    def test_global_scheduler_and_cycle_priority(self):
        subprocess.run([str(self.directory/'frontier')],check=True,capture_output=True,timeout=20)

    def test_actual_global_rules_pass_exact_replay(self):
        self.assertEqual(self.stats['global_mode'],4)
        self.assertGreater(self.stats['global_attempts'],0)
        self.assertGreater(self.stats['global_successes'],0)
        self.assertGreater(self.stats['retained_alternative_rules'],self.stats['imported_rules'])
        # Choose late rules to exercise new global proposals, rather than
        # merely replaying the imported local rules a second time.
        data=dict(self.data,alternative_rules=self.data['alternative_rules'][-24:])
        chosen=sample(data,24)
        audit=ScalarVerifier(chosen).audit()
        self.assertTrue(audit['verified_rules'])
        self.assertFalse(audit['failed_rules'])
        if self.data['closed_candidate']: ScalarVerifier(self.data).closed()
        self.assertEqual(len(supported(self.data)['supported_nodes']),self.stats['alternative_supported_nodes'])

    def test_global_priorities_survive_restart(self):
        native=self.directory/'again.txt'
        write_frontier(Path(str(self.output)+'.catalog.json'),native,self.cfg)
        output=self.directory/'resumed.json'
        history=Path(str(self.output)+'.global.txt')
        count=len(history.read_text().splitlines())-1
        self.run_native(output,native,5,history)
        stats=json.loads(Path(str(output)+'.feedback.json').read_text())
        self.assertEqual(stats['global_imported_attempt_keys'],count)
        self.assertEqual(stats['imported_alternatives'],len(self.data['alternative_rules']))


if __name__=='__main__':unittest.main()
