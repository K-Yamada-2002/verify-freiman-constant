"""Positive and adversarial controls for the integer overlap/closure engine.

These synthetic affine systems test the graph engine, not the 131 theorem.
"""
import json
import subprocess
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]
D=1<<48

def make(path,quarter=False,missing_endpoint=False):
    tails=[0,D//4,3*D//4,D] if quarter else [0,D//2,D]
    endpoints=[(0,len(tails)-1),(0,1),(len(tails)-2,len(tails)-1)]
    if missing_endpoint:endpoints[1:]=[(1,2),(1,2)]
    pairs=[(1,1,0),(1,2,0),(2,2,0)]
    lines=['FREIMAN_DYADIC_GRAPH_V1 1 3 0 0 1 3 0',f'0 {D}']
    lines+=[' '.join(map(str,p)) for p in pairs]
    lines += [f'{D} {D}',f'{D} {D}',f'{D} {D}',f'0 0 0 0 {len(tails)}']
    lines += [f'{t} {t}' for t in tails]
    for i,(l,h) in enumerate(endpoints):
        scale=D if i==0 else D//(2 if missing_endpoint or not quarter else 4)
        lines.append(f'0 0 {1 if i else 2} {scale} {scale} 0 {D} 0 {D} {l} {h}')
    path.write_text('\n'.join(lines)+'\n')

def make_centered(path,quarter=False,missing_endpoint=False):
    shift=3*D//8 if quarter else D//4
    if missing_endpoint:shift=0
    scale=D//(2 if missing_endpoint or not quarter else 4)
    lines=['BERSTEIN_ANCHOR_GRAPH_V1 1 3 0 0 1 3 0',f'{-D//2} {D//2}',
           '1 1 0','1 2 0','2 2 0',f'{D} {D}',f'{D} {D}',f'{D} {D}','0 0 0 1 3',
           f'{-shift} {-shift}','0 0',f'{shift} {shift}',
           f'0 0 2 {D} {D} 0 {D} 0 {D} 1 1',
           f'0 0 1 {scale} {scale} 0 {D} 0 {D} 0 0',
           f'0 0 1 {scale} {scale} 0 {D} 0 {D} 2 2']
    path.write_text('\n'.join(lines)+'\n')

def make_typed(path,quarter=False,missing_endpoint=False):
    make(path,quarter,missing_endpoint)
    lines=path.read_text().splitlines();head=lines[0].split()
    head[0]='BERSTEIN_T_GRAPH_V1';head[5]='5';lines[0]=' '.join(head)
    del lines[1]  # The typed engine has no fractional-band table.
    for i in range(len(lines)-3,len(lines)):
        row=lines[i].split();lines[i]=' '.join(row+row[-2:])
    path.write_text('\n'.join(lines)+'\n')

def main():
    reports=[]
    for engine,maker in [('graph_kernel',make),('anchor_kernel',make_centered),('t_kernel',make_typed)]:
      for short,quarter,missing,want in [('positive',False,False,True),
            ('gap',True,False,False),('endpoint',True,True,False)]:
        name=f'{engine}_{short}'
        inp=BASE/'data'/f'control_{name}.dat';out=inp.with_suffix('.json')
        maker(inp,quarter,missing)
        run=subprocess.run([str(BASE/'bin'/engine),str(inp),str(out)],capture_output=True,text=True)
        assert run.returncode==0,run.stderr
        report=json.loads(out.read_text())
        assert report['closed_family_found']==want
        if want:
            replay=subprocess.run([str(BASE/'bin'/engine),str(inp),str(out.with_name(f'control_{engine}_positive_replay.json')),str(out)+'.alive.bin'],capture_output=True,text=True)
            assert replay.returncode==0,replay.stderr
        else:
            h=inp.read_text().splitlines()[0].split()
            rows=int(h[1])**2*(int(h[4])-int(h[3])+1)*int(h[5])
            forged=BASE/'data'/f'control_{name}_forged.bin';forged.write_bytes(bytes([1])*rows)
            replay=subprocess.run([str(BASE/'bin'/engine),str(inp),str(out.with_name(f'control_{name}_must_fail.json')),str(forged)],capture_output=True,text=True)
            assert replay.returncode!=0 and 'not closed' in replay.stderr
        reports.append(dict(name=name,expected_nonempty=want,passed=True))
    # An absorbing past-3 violation makes all binary channels empty.
    inp=BASE/'data'/'control_t_past_violation.dat';out=inp.with_suffix('.json')
    make_typed(inp)
    lines=inp.read_text().splitlines()
    for i in range(len(lines)-3,len(lines)):
        row=lines[i].split();row[-2:]=['-1','-1'];lines[i]=' '.join(row)
    inp.write_text('\n'.join(lines)+'\n')
    run=subprocess.run([str(BASE/'bin'/'t_kernel'),str(inp),str(out)],capture_output=True,text=True)
    assert run.returncode==0 and json.loads(out.read_text())['root_types']==[1,0,0,0,0]
    reports.append(dict(name='t_kernel_past_violation',passed=True))
    (BASE/'data'/'controls.json').write_text(json.dumps(reports,indent=2)+'\n')
    print(json.dumps(reports))

if __name__=='__main__':main()
