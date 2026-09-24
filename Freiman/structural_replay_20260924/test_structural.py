"""Negative controls: removing each termination restriction must create a cycle."""
from pathlib import Path
import subprocess,tempfile,unittest

HERE=Path(__file__).resolve().parent

class TerminationControls(unittest.TestCase):
    def test_missing_forced_reflections_are_rejected(self):
        source=(HERE/'history_dag.c').read_text()
        mutations={
            'one_sided_2_or_3':'    if (a && !b && (a==2 || a==3) && nw==wide) return 0;\n',
            'two_consecutive_1':'    if (!wide && !e1 && a==1 && !b && (s&128) && nw!=1) return 0;\n',
            'nonwider_only_mixed':'    if (!a && p0==p1) return 0;\n',
        }
        for name,line in mutations.items():
            with self.subTest(name=name),tempfile.TemporaryDirectory(prefix='freiman-dag-control-') as tmp:
                self.assertEqual(source.count(line),1)
                path=Path(tmp)/'mutant.c';exe=Path(tmp)/'mutant'
                path.write_text(source.replace(line,''))
                subprocess.run(['cc','-std=c89','-O2',str(path),'-o',str(exe)],check=True,capture_output=True)
                result=subprocess.run([str(exe)],capture_output=True,text=True,timeout=5)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('FAIL: cycle',result.stderr)

if __name__=='__main__':unittest.main()
