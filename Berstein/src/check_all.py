"""Run the 131-language small proven results and engine controls; summarize completed searches.

This does not silently rerun the large exploratory searches, nor convert
their finite progress into an interval-inclusion certificate.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]

def main():
    (BASE/'bin').mkdir(exist_ok=True)
    for engine in ('graph_kernel','anchor_kernel','t_kernel'):
        subprocess.run(['clang++','-O3','-std=c++17',str(BASE/'src'/f'{engine}.cpp'),
                        '-o',str(BASE/'bin'/engine)],check=True)
    for name in ['verify_obstructions.py','verify_local.py','verify_forbidden_family.py',
                 'verify_t_endpoints.py','check_controls.py']:
        subprocess.run([sys.executable,'-B','-S',str(BASE/'src'/name)],check=True)
    searches=[]
    for name in ['m2','m3','fine','golden','centered','adaptive','golden_fine','t_kernel','t_fine']:
        result=BASE/'data'/f'{name}.json';meta=BASE/'data'/f'{name}.meta.json'
        if not meta.exists():continue
        m=json.loads(meta.read_text())
        rows=len(m['keys'])**2*(m['high']-m['low']+1)*len(m.get('bands',m.get('types')))
        entry=dict(name=name,rows=rows,memory=m['memory'],grid=m.get('grid'),base=m['base'],
                   anchor=m.get('anchor','lower'),centered=m.get('centered',False),
                   shape_tolerance=m.get('shape_tolerance'))
        if result.exists():
            r=json.loads(result.read_text());bits=Path(str(result)+'.alive.bin')
            entry.update(completed=True,surviving_rows=r['surviving_states'],
                         rounds=len(r['round_counts']),root_survives=any(r['root_types']))
            if bits.exists():
                data=bits.read_bytes()
                assert len(data)==rows and all(v in (0,1) for v in data)
                assert sum(data)==r['surviving_states']
        else:entry.update(completed=False)
        searches.append(entry)
    paths=sorted((BASE/'src').glob('*.py'))+sorted((BASE/'src').glob('*.cpp'))
    hashes={str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    report=dict(proved=['global-prefix T semantics','successor-cover implication',
                        'uniform suffix-13 obstruction','local T cover and root-cylinder gap'],
                KF_131_sum_interior_proved=False,searches=searches,source_snapshot_sha256=hashes,
                scope='131-language source snapshot and search output audit; the separate 31313 Markov interval proof is verified by verify_below_ray.py.')
    (BASE/'data'/'verification_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['searches']))

if __name__=='__main__':main()
