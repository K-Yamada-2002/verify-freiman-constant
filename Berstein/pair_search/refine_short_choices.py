#!/usr/bin/env python3
import json,subprocess,tempfile
from fractions import Fraction as Q
from pathlib import Path
from search import Model
from simple_sets import encode,bound_model
ROOT=Path(__file__).resolve().parent

def main():
 d=json.loads((ROOT/'short_rule_search.json').read_text());by={c['claim']:c for c in d['claims']};out={'choices':[]}
 with tempfile.TemporaryDirectory() as tmp:
  exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
  for number,index in [(2,0),(5,0),(9,2),(10,0)]:
   c=by[number]['coarse_candidates'][index];m=Model('short','123',c['forbidden']);a,b=[Q(str(x))-3 for x in c['target']]
   scan=json.loads(subprocess.run([str(exe),'9','1500000000'],input=encode(m,c['left'],c['right'],a,b),text=True,capture_output=True,check=True).stdout)
   item={k:v for k,v in c.items() if k!='scan'};item.update(claim=number,scan=scan)
   out['choices'].append(item);(ROOT/'short_choices_refined.json').write_text(json.dumps(out,indent=2)+'\n')
   print(number,c['forbidden'],scan['covers_target'],scan['complete'],scan['visited'],flush=True)
if __name__=='__main__':main()
