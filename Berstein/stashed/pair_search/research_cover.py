#!/usr/bin/env python3
"""Re-search threshold Cantor sets, keeping all cross-pair dominance checks."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import tempfile
from target_cover import ThresholdModel
from reduce_cover import background,dominance
from verify_reduced import forbidden_words
from refine_cover import prepare
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--radius',type=int,default=3);p.add_argument('--exponent',type=int,default=8)
    p.add_argument('--first-lo',default=None);p.add_argument('--claims',type=int,nargs='+',default=[1,3,7,9]);p.add_argument('--output',type=Path,default=ROOT/'research_r3.json')
    args=p.parse_args();old=json.loads((ROOT/'reduced_ten.json').read_text())
    out={'claims':[],'rejections':[]}
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
        for number in args.claims:
            c={k:old['claims'][number-1][k] for k in ('left','right','target')}
            if number==1 and args.first_lo:c['target']=[float(args.first_lo),c['target'][1]]
            floor=Q(str(c['target'][0]));H=floor-Q('0.000001')
            m=ThresholdModel(4,args.radius,H)
            if number==1:
                c['left']=['11','12'];c['right']=['11','12','21','22','2311','232','233']
            bound=max(background(m),dominance(m,tuple(c['left']),tuple(c['right'])))
            print('model',number,'bound',float(bound),'floor',float(floor),flush=True)
            if bound>=floor:
                out['rejections'].append(dict(claim=number,reason='dominance',bound=str(bound),model=m.metadata()))
            else:
                alphabet,forbidden=forbidden_words(m)
                definition=dict(label=f'R{number}',model=m.metadata(),graph=m.graph_signature,alphabet=alphabet,forbidden=forbidden)
                c.update(model=m.metadata(),graph=m.graph_signature,dominance_bound=str(bound))
                inp,pairs=prepare(definition,c)
                scan=json.loads(subprocess.run([str(exe),str(args.exponent),'2000000000'],input=inp,text=True,capture_output=True,check=True).stdout)
                out['claims'].append(dict(claim=number,definition=definition,proposition=c,scan=scan,language_state_pairs=pairs))
                print(number,scan['covers_target'],scan['complete'],scan['visited'],'forbidden',len(forbidden),flush=True)
            args.output.write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
