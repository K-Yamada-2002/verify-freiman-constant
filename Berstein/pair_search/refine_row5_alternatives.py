#!/usr/bin/env python3
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from simple_sets import encode
from search import Model
ROOT=Path(__file__).resolve().parent
cs=next(c['coarse_candidates'] for c in json.loads((ROOT/'short_rule_search.json').read_text())['claims'] if c['claim']==5)
out=[]
with tempfile.TemporaryDirectory() as tmp:
 exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
 for c in cs[1:]:
  m=Model('short','123',c['forbidden']);a,b=[Q(str(x))-3 for x in c['target']]
  scan=json.loads(subprocess.run([str(exe),'9','150000000'],input=encode(m,c['left'],c['right'],a,b),text=True,capture_output=True,check=True).stdout)
  item={k:v for k,v in c.items() if k!='scan'};item.update(claim=5,scan=scan);out.append(item)
  (ROOT/'row5_alternatives.json').write_text(json.dumps(out,indent=2)+'\n');print(c['forbidden'],scan['covers_target'],flush=True)
  if scan['covers_target']:break
