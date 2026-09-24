#!/usr/bin/env python3
"""Assemble replacement propositions and certify each whole interval anew."""
import argparse,hashlib,json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from refine_cover import prepare
ROOT=Path(__file__).resolve().parent

def assemble():
    old=json.loads((ROOT/'reduced_ten.json').read_text())['claims']
    defs={d['graph']:d for d in json.loads((ROOT/'reduced_ten_audit.json').read_text())['definitions']}
    repairs={c['claim']:c for c in json.loads((ROOT/'research_r3.json').read_text())['claims']}
    split=json.loads((ROOT/'research_first_split.json').read_text())['claims'][0]
    for r in list(repairs.values())+[split]:defs[r['definition']['graph']]=r['definition']
    rows=[]
    for i,c in enumerate(old,1):
        if i in repairs:c=repairs[i]['proposition']
        c={k:c[k] for k in ('left','right','target','model','graph','dominance_bound')}
        c['origin']=i
        if i==1:
            c['target']=[4.1,4.124769];rows.append(c)
            s={k:split['proposition'][k] for k in ('left','right','target','model','graph','dominance_bound')}
            s['origin']='1b';rows.append(s)
        else:
            rows.append(c)
    return rows,defs

def main():
    p=argparse.ArgumentParser();p.add_argument('--exponent',type=int,default=9);p.add_argument('--output',type=Path,default=ROOT/'rebuilt_cover.json');args=p.parse_args()
    rows,defs=assemble()
    out={'status':'Unproved inclusion candidates; exact finite-distance checks only','exponent':args.exponent,
         'cpp_sha256':hashlib.sha256((ROOT/'refine_cover.cpp').read_bytes()).hexdigest(),'definitions':list({c['graph']:defs[c['graph']] for c in rows}.values()),'claims':[]}
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
        for i,c in enumerate(rows,1):
            inp,pairs=prepare(defs[c['graph']],c)
            scan=json.loads(subprocess.run([str(exe),str(args.exponent),'2500000000'],input=inp,text=True,capture_output=True,check=True).stdout)
            c['scan']=scan;c['language_state_pairs']=pairs;c['input_sha256']=hashlib.sha256(inp.encode()).hexdigest()
            c['rational_leaf_check']={'covered':[[str(Q(a,scan['scale'])+3),str(Q(b,scan['scale'])+3)] for a,b in scan['covered']],
                                      'maximum_width':str(Q(scan['max_width_units'],scan['scale']))}
            out['claims'].append(c);args.output.write_text(json.dumps(out,indent=2)+'\n')
            print(i,c['origin'],scan['covers_target'],scan['complete'],scan['visited'],scan['seconds'],flush=True)
if __name__=='__main__':main()
