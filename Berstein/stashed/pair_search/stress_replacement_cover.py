#!/usr/bin/env python3
"""Whole-neighborhood 1e-12 cover around every former rigorous gap."""
import argparse,json,subprocess,tempfile
from fractions import Fraction as Q
from pathlib import Path
from search import merge
from refine_cover import prepare,S
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,default=ROOT/'replacement_1e8.json');args=p.parse_args()
    d=json.loads(args.input.read_text());defs={x['graph']:x for x in d['definitions']}
    old=json.loads((ROOT/'refined_gap_certificates.json').read_text())
    intervals=[]
    for c in old:
        a,b=map(Q,c['excluded_closed_interval'])
        intervals.append((Q((a*S).numerator//(a*S).denominator,S)-Q('0.0000001'),Q(-(-(b*S).numerator//(b*S).denominator),S)+Q('0.0000001')))
    results=[]
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
        for a,b in merge(intervals):
            options=[(i,c) for i,c in enumerate(d['claims'],1) if Q(str(c['target'][0]))<=a+3 and b+3<=Q(str(c['target'][1]))]
            assert options
            i,c=options[0];c=c.copy();c['target']=[str(a+3),str(b+3)]
            inp,pairs=prepare(defs[c['graph']],c)
            scan=json.loads(subprocess.run([str(exe),'12','200000000'],input=inp,text=True,capture_output=True,check=True).stdout)
            results.append(dict(claim=i,target_sum=[str(a),str(b)],scan=scan))
            print(i,float(a),float(b),scan['covers_target'],scan['complete'],scan['visited'],flush=True)
    (ROOT/'replacement_stress_1e12.json').write_text(json.dumps({'source':str(args.input),'neighborhoods':results},indent=2)+'\n')
if __name__=='__main__':main()
