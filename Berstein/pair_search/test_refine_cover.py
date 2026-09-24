import json
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import tempfile
import unittest
from search import Model,matrix
from refine_cover import S

class IntegerCoverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory()
        cls.exe=Path(cls.tmp.name)/'cover'
        subprocess.run(['c++','-O2','-std=c++17',str(Path(__file__).with_name('refine_cover.cpp')),'-o',str(cls.exe)],check=True)
    @classmethod
    def tearDownClass(cls): cls.tmp.cleanup()
    def test_endpoints_against_independent_fraction(self):
        m=Model('test','123',('131',))
        states={s:i for i,s in enumerate(m.states)}
        bounds=m.tail_bounds(Q,20);grid={}
        rows=[f'{len(states)} {S} {2*S}']
        for s in m.states:
            lo,hi=bounds[s];lo=int(lo*S);hi=-int((-hi*S)//1)
            grid[s]=(Q(lo,S),Q(hi,S));es=dict(m.edges[s])
            rows.append(' '.join(map(str,[lo,hi]+[states[es[k]] if k in es else -1 for k in '123'])))
        words=[z[0] for z in m.cylinders('',5)]+['2'*15,'123'*6]
        inp='\n'.join(rows+[str(len(words))]+words+['1','2'])+'\n'
        actual=json.loads(subprocess.run([str(self.exe),'8','100','--prefixes'],input=inp,text=True,capture_output=True,check=True).stdout)
        for w,pair in zip(words,actual):
            a,b,c,d=matrix(w);lo,hi=sorted((a*t+b)/(c*t+d) for t in grid[m.follow(w)])
            self.assertEqual(pair,[int(lo*S),-int((-hi*S)//1)])
    def test_budget_does_not_claim_completion(self):
        inp=f'1 {S} {2*S}\n{S//4} {4*S//5} 0 0 0\n1\n1\n1\n2\n'
        out=json.loads(subprocess.run([str(self.exe),'8','0'],input=inp,text=True,capture_output=True,check=True).stdout)
        self.assertFalse(out['complete']);self.assertFalse(out['covers_target'])
