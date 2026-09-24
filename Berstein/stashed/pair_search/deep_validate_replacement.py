#!/usr/bin/env python3
"""Reproducible local whole-interval tests, not a full-target finer cover."""
import argparse,hashlib,json,random,subprocess,tempfile
from fractions import Fraction as Q
from pathlib import Path
from refine_cover import prepare,S
from search import merge
ROOT=Path(__file__).resolve().parent

def windows(c,number):
    lo,hi=[int((Q(str(x))-3)*S) for x in c['target']]
    # Fixed grid and fixed pseudo-random seed are recorded and reproducible.
    centers={lo,hi}|{lo+(hi-lo)*k//17 for k in range(1,17)}
    rng=random.Random(20260924+number)
    centers|={rng.randrange(lo,hi+1) for _ in range(16)}
    half=5_000_000  # radius 5e-9; window length 1e-8
    out=[(max(lo,t-half),min(hi,t+half)) for t in sorted(centers)]
    old=json.loads((ROOT/'refined_gap_certificates.json').read_text())
    old.append(json.loads((ROOT/'rejected_second_gap.json').read_text()))
    for g in old:
        a,b=map(Q,g['excluded_closed_interval'])
        a=int(a*S)-100_000_000;b=-int((-b*S)//1)+100_000_000
        if lo<=a and b<=hi:out.append((a,b))
    return merge(out)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--exponent',type=int,default=13);args=ap.parse_args()
    source=ROOT/'replacement_cover.json';data=json.loads(source.read_text());defs={d['graph']:d for d in data['definitions']}
    results={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
             'cpp_sha256':hashlib.sha256((ROOT/'deep_cover.cpp').read_bytes()).hexdigest(),
             'meaning':'Local windows only: does not upgrade the full-target 1e-9 guarantee.',
             'seed':20260924,'exponent':args.exponent,'claims':[]}
    with tempfile.TemporaryDirectory(prefix='deep-cover-') as tmp:
        exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'deep_cover.cpp'),'-o',str(exe)],check=True)
        for i,c in enumerate(data['claims'],1):
            template,pairs=prepare(defs[c['graph']],c);header,rest=template.split('\n',1);n=header.split()[0]
            entry={'claim':i,'language_state_pairs':pairs,'windows':[]};results['claims'].append(entry)
            for a,b in windows(c,i):
                inp=f'{n} {a} {b}\n'+rest
                run=subprocess.run([str(exe),str(args.exponent),'100000000'],input=inp,text=True,capture_output=True)
                scan=json.loads(run.stdout) if run.returncode==0 else {'error':run.stderr,'complete':False,'covers_target':False}
                entry['windows'].append({'target_sum':[str(Q(a,S)),str(Q(b,S))],'scan':scan})
            (ROOT/'replacement_deep_windows.json').write_text(json.dumps(results,indent=2)+'\n')
            failed=[w for w in entry['windows'] if not w['scan']['covers_target'] or not w['scan']['complete']]
            print('claim',i,'windows',len(entry['windows']),'failed',len(failed),'nodes',sum(w['scan'].get('visited',0) for w in entry['windows']),flush=True)
if __name__=='__main__':main()
