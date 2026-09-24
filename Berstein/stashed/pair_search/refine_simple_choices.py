#!/usr/bin/env python3
import json,subprocess,tempfile
from fractions import Fraction as Q
from pathlib import Path
from simple_sets import bound_model,encode
from search import Model
ROOT=Path(__file__).resolve().parent

def main():
 original=json.loads((ROOT/'replacement_cover.json').read_text())['claims']
 choices=[(3,['131','2313','3132','21323','32312']), (6,['131','313'])]
 out={'choices':[]}
 with tempfile.TemporaryDirectory() as tmp:
  exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
  for number,ws in choices:
   c=original[number-1];m,bound=bound_model(ws,c);a,b=[Q(str(x))-3 for x in c['target']];assert bound<a+3
   scan=json.loads(subprocess.run([str(exe),'9','1500000000'],input=encode(m,c['left'],c['right'],a,b),text=True,capture_output=True,check=True).stdout)
   out['choices'].append(dict(claim=number,forbidden=ws,left=c['left'],right=c['right'],target=c['target'],dominance_bound=str(bound),scan=scan))
   (ROOT/'simple_choices_refined.json').write_text(json.dumps(out,indent=2)+'\n');print(number,scan['covers_target'],scan['complete'],scan['visited'],flush=True)
  m=Model('KF','123',['131']);scan=json.loads(subprocess.run([str(exe),'9','1500000000'],input=encode(m,['1','2','3'],['1','2','3'],'1.27','1.36'),text=True,capture_output=True,check=True).stdout)
  out['kf']={'forbidden':['131'],'left':['1','2','3'],'right':['1','2','3'],'target':[4.27,4.36],'dominance_bound':'191/45','scan':scan}
  (ROOT/'simple_choices_refined.json').write_text(json.dumps(out,indent=2)+'\n');print('KF',scan['covers_target'],scan['complete'],scan['visited'],flush=True)
if __name__=='__main__':main()
