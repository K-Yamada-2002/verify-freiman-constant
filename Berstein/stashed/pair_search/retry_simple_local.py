#!/usr/bin/env python3
"""Increase budgets on incomplete local scans; never call them counterexamples."""
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from audit_simple_cover import model,ROOT
from simple_sets import encode
p=ROOT/'simple_cover_local_audit.json';data=json.loads(p.read_text());source=json.loads((ROOT/'simple_cover.json').read_text());assert len(data['claims'])==11
with tempfile.TemporaryDirectory() as tmp:
 exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'deep_cover.cpp'),'-o',str(exe)],check=True)
 for entry in data['claims']:
  c=source['claims'][entry['claim']-1];m=model(c);L=['1','2','3'] if c['left']==[''] else c['left'];R=['1','2','3'] if c['right']==[''] else c['right']
  for w in entry['windows']:
   s=w['scan']
   if s['complete'] and s['covers_target']:continue
   w.setdefault('earlier_attempts',[]).append({k:v for k,v in s.items() if k!='covered'})
   a,b=map(Q,w['target_sum']);r=json.loads(subprocess.run([str(exe),'13','250000000'],input=encode(m,L,R,a,b),text=True,capture_output=True,check=True).stdout)
   w['scan']=r;p.write_text(json.dumps(data,indent=2)+'\n');print('retry',entry['claim'],r['complete'],r['covers_target'],r['visited'],flush=True)
