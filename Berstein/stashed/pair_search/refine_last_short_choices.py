#!/usr/bin/env python3
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from search import Model
from simple_sets import encode
ROOT=Path(__file__).resolve().parent
out=[]
with tempfile.TemporaryDirectory() as tmp:
 exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
 for n,name in [(5,'short_rule_row5_allow131.json'),(7,'short_rule_row7.json')]:
  cs=json.loads((ROOT/name).read_text())['claims'][0]['coarse_candidates']
  for c in cs:
   m=Model('short','123',c['forbidden']);a,b=[Q(str(x))-3 for x in c['target']]
   scan=json.loads(subprocess.run([str(exe),'9','500000000'],input=encode(m,c['left'],c['right'],a,b),text=True,capture_output=True,check=True).stdout)
   item={k:v for k,v in c.items() if k!='scan'};item.update(claim=n,scan=scan);out.append(item)
   (ROOT/'last_short_choices_refined.json').write_text(json.dumps(out,indent=2)+'\n');print(n,c['forbidden'],scan['covers_target'],scan['complete'],scan['visited'],flush=True)
   if scan['covers_target'] and scan['complete']:break
