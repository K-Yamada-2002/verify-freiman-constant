#!/usr/bin/env python3
"""Compare small forbidden-word catalogues on the existing target intervals."""
import json,subprocess,tempfile
from pathlib import Path
from fractions import Fraction as Q
from search import Model,catalogue
from reduce_cover import dominance
from simple_sets import encode
ROOT=Path(__file__).resolve().parent

def main():
 d=json.loads((ROOT/'replacement_cover.json').read_text());defs={x['graph']:x for x in d['definitions']}
 words={tuple(sorted(m.forbidden)) for m in catalogue() if m.alphabet=='123'}
 words|={tuple(sorted(x['forbidden'])) for x in d['definitions'] if len(x['forbidden'])<=7}
 words|={('131','2313','3132'),('1312','1313','2131','3131')}
 models=[]
 for ws in sorted(words,key=lambda ws:(len(ws),sum(map(len,ws)),ws)):
  m=Model('simple','123',ws);m.digits=3;m.radius=4;m.cert_bounds=m.tail_bounds(Q,16);bg=m.background(4)[0];models.append((m,bg))
 out={'meaning':'Coarse discovery only, no replacement without further checks','claims':[]}
 with tempfile.TemporaryDirectory() as tmp:
  exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
  for i,c in enumerate(d['claims'],1):
   floor=Q(str(c['target'][0]));hi=Q(str(c['target'][1]));entry={'claim':i,'candidates':[]};out['claims'].append(entry)
   for m,bg in models:
    if bg>=floor:continue
    left=[w for w in c['left'] if m.follow(w) is not None];right=[w for w in c['right'] if m.follow(w) is not None]
    if not left or not right:continue
    bound=max(bg,dominance(m,tuple(left),tuple(right)))
    if bound>=floor:continue
    scan=json.loads(subprocess.run([str(exe),'7','15000000'],input=encode(m,left,right,floor-3,hi-3),text=True,capture_output=True,check=True).stdout)
    candidate={'forbidden':m.forbidden,'left':left,'right':right,'dominance_bound':str(bound),'scan':scan}
    entry['candidates'].append(candidate)
    print(i,len(m.forbidden),m.forbidden,'covers',scan['covers_target'], 'complete',scan['complete'],flush=True)
   (ROOT/'simple_catalogue_search.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
