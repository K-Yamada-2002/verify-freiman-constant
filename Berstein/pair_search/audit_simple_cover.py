#!/usr/bin/env python3
"""Audit the final simple family using minimal forbidden-word automata."""
import argparse,hashlib,json,random,subprocess,tempfile
from collections import Counter
from decimal import Decimal,localcontext
from fractions import Fraction as Q
from pathlib import Path
from search import Model,merge
from simple_sets import encode
from target_cover import complement
from reduce_cover import dominance
from verify_target_cover import find_witness,certify
ROOT=Path(__file__).resolve().parent;S=10**15

def critical_points():
 old=json.loads((ROOT/'refined_gap_certificates.json').read_text())+[json.loads((ROOT/'rejected_second_gap.json').read_text())]
 points=set();neighborhoods=[]
 for g in old:
  a,b=map(Q,g['excluded_closed_interval']);points.update(a+(b-a)*k/4 for k in range(5));neighborhoods.append((a,b))
 failed=json.loads((ROOT/'short_choices_refined.json').read_text())['choices']+json.loads((ROOT/'last_short_choices_refined.json').read_text())+json.loads((ROOT/'row5_alternatives.json').read_text())
 for c in failed:
  s=c['scan']
  if s['covers_target'] or not s['complete']:continue
  a,b=[Q(str(x))-3 for x in c['target']]
  gs=complement([(Q(x,s['scale']),Q(y,s['scale'])) for x,y in s['covered']],a,b)
  for x,y in gs:points.add((x+y)/2);neighborhoods.append((x,y))
 return points,neighborhoods

def model(c):
 m=Model(c['label'],'123',c['forbidden']);m.digits=3;m.radius=4;m.cert_bounds=m.tail_bounds(Q,16);m.reset=m.follow('2'*9)
 return m

def verify(d):
 intervals=[]
 for c in d['claims']:
  m=model(c);bound=max(m.background(4)[0],dominance(m,tuple(c['left']),tuple(c['right'])))
  assert bound==Q(c['dominance_bound'])
  a,b=[Q(str(x)) for x in c['target']];w=Q(c['rational_leaf_check']['maximum_width'])
  assert bound+w<a and w<=Q(1,10**9)
  assert not complement([tuple(map(Q,z)) for z in c['rational_leaf_check']['covered']],a,b)
  intervals.append((a,b))
 assert not complement(intervals,Q('4.1'),Q('4.52'))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['points','local']);args=ap.parse_args()
 source=ROOT/'simple_cover.json';data=json.loads(source.read_text());verify(data);critical,near=critical_points()
 result={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'mode':args.mode,'claims':[]}
 if args.mode=='points':
  witnesses=[];unresolved=[]
  with localcontext() as ctx:
   ctx.prec=80
   for c in data['claims']:
    m=model(c);bd=m.tail_bounds(Decimal,240);a,b=[Q(str(x)) for x in c['target']]
    targets={a+(b-a)*k/1000 for k in range(1001)}|{3+p for p in critical if a<=3+p<=b}
    for t in sorted(targets):
     offers=[];td=Decimal(t.numerator)/Decimal(t.denominator)-3
     for u in c['left']:
      for v in c['right']:
       x,y=m.cylinder(u,bd),m.cylinder(v,bd)
       if x[3]+y[3]<=td<=x[4]+y[4]:offers.append((min(td-x[3]-y[3],x[4]+y[4]-td),u,v))
     found=None
     for _,u,v in sorted(offers,reverse=True):
      found=find_witness(m,dict(center=3,u=u,v=v),t,bd,budget=100000)
      if found:break
     if found:
      x,y=certify(m,found['u'],found['root_u']);z,w=certify(m,found['v'],found['root_v']);assert max(abs(3+x+z-t),abs(3+y+w-t))==Q(found['error_bound'])<Q(1,10**30)
      found['claim']=c['claim'];witnesses.append(found)
     else:unresolved.append({'claim':c['claim'],'target':str(t)})
    print('points',c['claim'],len(witnesses),'unresolved',len(unresolved),flush=True)
  result.update(witnesses=witnesses,unresolved=unresolved)
 else:
  with tempfile.TemporaryDirectory() as tmp:
   exe=Path(tmp)/'scan';subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'deep_cover.cpp'),'-o',str(exe)],check=True)
   for c in data['claims']:
    m=model(c);a,b=[int((Q(str(x))-3)*S) for x in c['target']];rng=random.Random(20260924+c['claim'])
    centers={a,b}|{a+(b-a)*k//17 for k in range(1,17)}|{rng.randrange(a,b+1) for _ in range(16)}
    iv=[(max(a,t-5000000),min(b,t+5000000)) for t in centers]
    for x,y in near:
     x=int(x*S)-100000000;y=-int((-y*S)//1)+100000000
     if a<=x and y<=b:iv.append((x,y))
    L=['1','2','3'] if c['left']==[''] else c['left'];R=['1','2','3'] if c['right']==[''] else c['right']
    template=encode(m,L,R,Q(a,S),Q(b,S));head,rest=template.split('\n',1);n=head.split()[0];entry={'claim':c['claim'],'windows':[]}
    for x,y in merge(iv):
     run=subprocess.run([str(exe),'13','100000000'],input=f'{n} {x} {y}\n'+rest,text=True,capture_output=True)
     s=json.loads(run.stdout) if run.returncode==0 else {'error':run.stderr,'complete':False,'covers_target':False}
     entry['windows'].append({'target_sum':[str(Q(x,S)),str(Q(y,S))],'scan':s})
    result['claims'].append(entry);bad=sum(not w['scan']['complete'] or not w['scan']['covers_target'] for w in entry['windows'])
    (ROOT/'simple_cover_local_audit.json').write_text(json.dumps(result,indent=2)+'\n');print('local',c['claim'],len(entry['windows']),'failed',bad,flush=True)
 (ROOT/f'simple_cover_{args.mode}_audit.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
