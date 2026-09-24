#!/usr/bin/env python3
"""Finer full-interval scan of selected final propositions; expensive for wide I."""
import argparse,hashlib,json,subprocess,tempfile
from pathlib import Path
from refine_cover import prepare
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--claim',type=int,required=True);p.add_argument('--exponent',type=int,required=True);p.add_argument('--budget',type=int,default=2500000000);args=p.parse_args()
    source=ROOT/'replacement_cover.json';d=json.loads(source.read_text());c=d['claims'][args.claim-1];defs={x['graph']:x for x in d['definitions']}
    inp,pairs=prepare(defs[c['graph']],c)
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'deep_cover.cpp'),'-o',str(exe)],check=True)
        run=subprocess.run([str(exe),str(args.exponent),str(args.budget)],input=inp,text=True,capture_output=True,check=True)
    result={'claim':args.claim,'target':c['target'],'language_state_pairs':pairs,
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(inp.encode()).hexdigest(),
            'cpp_sha256':hashlib.sha256((ROOT/'deep_cover.cpp').read_bytes()).hexdigest(),'scan':json.loads(run.stdout)}
    (ROOT/f'replacement_full_{args.claim}_1e{args.exponent}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(args.claim,result['scan'],flush=True)
if __name__=='__main__':main()
