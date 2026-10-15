"""Controls separating a closed family, an empty one, and a budget stop."""
import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path
from check_independent_kernel import make_input


def main():
    p=argparse.ArgumentParser()
    p.add_argument('binary',type=Path)
    args=p.parse_args()
    binary=args.binary.resolve()
    pairs=[(1,1),(1,2),(2,1),(2,2)]
    layered=make_input(pairs,states=2,child=1).splitlines()
    layered[-2:]=['-1','-1']
    layered='\n'.join(layered)+'\n'
    cases=[('closed',make_input(pairs),1,True,False,1),
           ('partial',layered,1,False,True,1),
           ('empty',layered,3,False,False,0)]
    reports=[]
    with tempfile.TemporaryDirectory(prefix='berstein-bounded-controls-') as directory:
        folder=Path(directory)
        for name,source,limit,closed,reached,total in cases:
            inp,out=folder/(name+'.dat'),folder/(name+'.json')
            inp.write_text(source)
            subprocess.run([str(binary),str(inp),str(out),'--round-limit',str(limit)],
                           check=True,stdout=subprocess.DEVNULL)
            result=json.loads(out.read_text())
            assert (result['closed_family_found'],result['round_limit_reached'],
                    result['surviving_states'])==(closed,reached,total)
            reports.append(dict(name=name,result=result))
    root=Path(__file__).resolve().parents[2]
    sources=[Path(__file__).resolve(),root/'Berstein/src/exploration_kernel.cpp',binary]
    report=dict(passed=True,cases=reports,
                scope='Artificial status controls, not continued-fraction semantics.',
                sha256={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sources})
    (root/'Berstein/data/exploration_bounded_controls.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Closed, partial-at-budget, and empty cases classified correctly')


if __name__=='__main__':main()
