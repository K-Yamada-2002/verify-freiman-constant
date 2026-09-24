import json
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import tempfile
import unittest

class DeepPrecisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory();cls.exe=Path(cls.tmp.name)/'scan'
        subprocess.run(['c++','-O2','-std=c++17',str(Path(__file__).with_name('deep_cover.cpp')),'-o',str(cls.exe)],check=True)
    @classmethod
    def tearDownClass(cls):cls.tmp.cleanup()
    def run_point(self,t,word='2'):
        # Only digit 2 is legal, so the exact sum is 2*sqrt(2)-2.
        s=10**15;inp=f'1 {t} {t}\n{s//4} {4*s//5} -1 0 -1\n1\n{word}\n1\n{word}\n'
        return subprocess.run([str(self.exe),'13','10000'],input=inp,text=True,capture_output=True)
    def test_thirteenth_decimal_scale(self):
        t=Q(828427124746190,10**15);eps=Q(1,10**13)
        self.assertLess((1+(t-eps)/2)**2,2);self.assertGreater((1+(t+eps)/2)**2,2)
        run=self.run_point(828427124746190);self.assertEqual(run.returncode,0,run.stderr)
        d=json.loads(run.stdout);self.assertTrue(d['complete']);self.assertTrue(d['covers_target']);self.assertLessEqual(d['max_width_units'],100)
    def test_exactly_excluded_point(self):
        d=json.loads(self.run_point(900000000000000).stdout)
        self.assertTrue(d['complete']);self.assertFalse(d['covers_target'])
    def test_overflow_fails_closed(self):
        r=self.run_point(828427124746190,'2'*60)
        self.assertNotEqual(r.returncode,0);self.assertIn('overflow',r.stderr)
