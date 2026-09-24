#!/usr/bin/env python3
"""Strengthen long rules into short ones, testing known trouble points first."""
import argparse,json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from search import Model
from simple_sets import encode
ROOT=Path(__file__).resolve().parent

def canonical(ws):
 return tuple(sorted(w for w in set(ws) if not any(v!=w and v in w for v in set(ws))))
def variants(ws):
 out=set()
 for w in ws:
  for n in range(2,len(w)):
   for k in range(len(w)-n+1):
    v=w[k:k+n];out.add(canonical(set(ws)|{v,v[::-1]}))
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--claims',type=int,nargs='+',default=[2,3,5,9,10]);ap.add_argument('--allow-131',action='store_true');ap.add_argument('--output',type=Path,default=ROOT/'short_rule_search.json');args=ap.parse_args()
 data=json.loads((ROOT/'replacement_cover.json').read_text());defs={d['graph']:d for d in data['definitions']}
 trouble=json.loads((ROOT/'refined_gap_certificates.json').read_text())+[json.loads((ROOT/'rejected_second_gap.json').read_text())]
 points=[sum(map(Q,g['excluded_closed_interval']))/2 for g in trouble]
 points.append(sum(map(Q,json.loads((ROOT/'kf_cylinder_check.json').read_text())['rigorous_counterexample']['interval']))/2)
 result={'claims':[]}
 with tempfile.TemporaryDirectory() as tmp:
  exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
  for number in args.claims:
   c=data['claims'][number-1];original=defs[c['graph']]['forbidden'];a,b=[Q(str(x))-3 for x in c['target']]
   first=variants(original);proposed=first|set().union(*(variants(ws) for ws in sorted(first,key=lambda x:(len(x),sum(map(len,x))))[:30]))
   proposed=sorted((ws for ws in proposed if len(ws)<=8),key=lambda ws:(len(ws),sum(map(len,ws)),ws))
   tests=[p for p in points if a<=p<=b]+[a,b,(a+b)/2];tests=[Q(round(t*10**15),10**15) for t in tests]
   entry={'claim':number,'tried':0,'coarse_candidates':[]};result['claims'].append(entry)
   for ws in proposed:
    if args.allow_131 and any(v in '131' for v in ws):continue
    # Every old forbidden word contains a new forbidden word: exact subset.
    assert all(any(v in w for v in ws) for w in original)
    try:m=Model('short','123',ws)
    except ValueError:continue
    left=[w for w in c['left'] if m.follow(w) is not None];right=[w for w in c['right'] if m.follow(w) is not None]
    if not left or not right:continue
    entry['tried']+=1;ok=True
    for t in tests:
     r=json.loads(subprocess.run([str(exe),'12','30000'],input=encode(m,left,right,t,t),text=True,capture_output=True,check=True).stdout)
     if not r['covers_target']:ok=False;break
    if not ok:continue
    scan=json.loads(subprocess.run([str(exe),'7','15000000'],input=encode(m,left,right,a,b),text=True,capture_output=True,check=True).stdout)
    if scan['covers_target'] and scan['complete']:
     entry['coarse_candidates'].append({'forbidden':ws,'left':left,'right':right,'scan':scan,'dominance_bound':c['dominance_bound'],'target':c['target'],'subset_of_original':True})
     print('FOUND',number,ws,flush=True)
     if len(entry['coarse_candidates'])>=3:break
   print('row',number,'tried',entry['tried'],'found',len(entry['coarse_candidates']),flush=True)
   args.output.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
