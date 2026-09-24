#!/usr/bin/env python3
"""Run bounded floating band searches; independently verify positive candidates."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from verify_scalar_graph import verifier_for


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--engine',type=Path,required=True)
    ap.add_argument('--plan',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=180)
    args=ap.parse_args(); args.output_dir.mkdir(parents=True,exist_ok=True)
    summary=dict(engine_sha256=hashlib.sha256(args.engine.read_bytes()).hexdigest(),results=[],closed=False)
    for i,cfg in enumerate(json.loads(args.plan.read_text())):
        target=args.output_dir/f'stage_{i:02}.json'; start=time.monotonic()
        if target.exists(): raise ValueError('use a fresh output directory; stale outputs are not candidates')
        command=[str(args.engine.resolve())]+[str(cfg[k]) for k in ('memory','bins','base','length','grid','rounds')]+[str(target),cfg['tilt']]
        row=dict(settings=cfg,closed=False)
        with target.with_suffix('.log').open('w') as log:
            try:
                subprocess.run(command,stdout=log,stderr=log,timeout=args.seconds,check=True)
                row['stop']='engine completed'
            except subprocess.TimeoutExpired: row['stop']='time limit'
            except subprocess.CalledProcessError as error:
                row.update(stop='engine failed',exit_code=error.returncode)
        if target.exists():
            data=json.loads(target.read_text())
            row.update(history=data['history'],nodes=len(data['nodes']),floating_closed_candidate=data['closed_candidate'])
            if data['closed_candidate']:
                try:
                    row['verification']=verifier_for(data).closed(); row['closed']=True
                except ValueError as error: row['exact_rejection']=str(error)
        partial=Path(str(target)+'.last_nonempty.json')
        if partial.exists():
            candidate=json.loads(partial.read_text()); checker=verifier_for(candidate)
            checks=[]; failures=[]
            for j,n in enumerate(candidate['nodes']):
                if n['covered']:
                    try: checks.append(checker.local(j))
                    except ValueError as error: failures.append(dict(node=j,error=str(error)))
            row['last_nonempty_audit']=dict(source=str(partial),nodes=len(candidate['nodes']),
                                           verified=checks,failed=failures,closed=False)
        row['elapsed_seconds']=time.monotonic()-start
        summary['results'].append(row); summary['closed']|=row['closed']
        (args.output_dir/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps({k:v for k,v in row.items() if k not in ('history','last_nonempty_audit','verification')}),flush=True)
        if row['closed']: break


if __name__=='__main__': main()
