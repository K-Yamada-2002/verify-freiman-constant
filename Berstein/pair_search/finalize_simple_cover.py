#!/usr/bin/env python3
"""Assemble the simple cover, then safely enlarge its prefix factors."""
import hashlib,json
from pathlib import Path
from fractions import Fraction as Q
from search import Model,merge
from reduce_cover import dominance,antichain
from target_cover import complement
ROOT=Path(__file__).resolve().parent

def evidence(c):
 if 'rational_leaf_check' in c:
  q=c['rational_leaf_check'];return [tuple(map(Q,z)) for z in q['covered']],Q(q['maximum_width'])
 s=c['scan'];assert s['complete'] and s['covers_target']
 return [(Q(a,s['scale'])+3,Q(b,s['scale'])+3) for a,b in s['covered']],Q(s['max_width_units'],s['scale'])

def main():
 old=json.loads((ROOT/'replacement_cover.json').read_text());defs={d['graph']:d for d in old['definitions']}
 simple=json.loads((ROOT/'simple_choices_refined.json').read_text())
 choices={c['claim']:c for c in simple['choices'] if c['scan']['covers_target']}
 choices.update({c['claim']:c for c in json.loads((ROOT/'short_choices_refined.json').read_text())['choices'] if c['scan']['covers_target']})
 choices.update({c['claim']:c for c in json.loads((ROOT/'last_short_choices_refined.json').read_text()) if c['scan']['covers_target']})
 rows=[]
 for number,c in enumerate(old['claims'][:8],1):
  s=choices.get(number,c);ws=s.get('forbidden',defs[c['graph']]['forbidden'])
  target=list(c['target'])
  if number==8:target[1]=4.270001
  rows.append(dict(forbidden=sorted(ws),left=s['left'],right=s['right'],target=target,sources=[s],origin=[number]))
 kf=simple['kf'];assert kf['scan']['covers_target'];rows.append(dict(forbidden=['131'],left=[''],right=[''],target=kf['target'],sources=[kf],origin=['KF']))
 a,b=choices[9],choices[10];assert set(a['forbidden'])==set(b['forbidden'])
 rows.append(dict(forbidden=sorted(a['forbidden']),left=antichain(a['left']+b['left']),right=antichain(a['right']+b['right']),target=[a['target'][0],b['target'][1]],sources=[a,b],origin=[9,10]))
 c=old['claims'][10];rows.append(dict(forbidden=sorted(defs[c['graph']]['forbidden']),left=c['left'],right=c['right'],target=c['target'],sources=[c],origin=[11]))
 definitions={};output=[]
 for number,row in enumerate(rows,1):
  ws=tuple(row['forbidden']);m=Model('simple','123',ws);m.digits=3;m.radius=4;m.cert_bounds=m.tail_bounds(Q,16);bg=m.background(4)[0]
  floor,ceil=map(lambda x:Q(str(x)),row['target']);eps=Q(1,10**9)
  left,right=antichain(row['left']),antichain(row['right'])
  upper=lambda L,R:max(bg,dominance(m,tuple(L),tuple(R)))
  assert upper(left,right)+eps<floor
  # Remove prefix restrictions only when every newly admitted cross pair is safe.
  history=[]
  while True:
   proposals=[]
   for side,factor in enumerate((left,right)):
    for w in factor:
     if not w:continue
     new=antichain([p for p in factor if p!=w]+[w[:-1]])
     L,R=(new,right) if side==0 else (left,new)
     value=upper(L,R)
     if value+eps<floor:proposals.append(((len(L)+len(R),sum(map(len,L))+sum(map(len,R))),L,R,value))
   if not proposals:break
   _,left,right,value=min(proposals)
   history.append(dict(left=left,right=right,upper=str(value)))
  intervals=[];width=Q(0)
  for src in row['sources']:
   assert all(any(w.startswith(p) for p in left) for w in src['left'])
   assert all(any(w.startswith(p) for p in right) for w in src['right'])
   iv,w=evidence(src);intervals+=iv;width=max(width,w)
  intervals=[(max(floor,a),min(ceil,b)) for a,b in merge(intervals) if a<=ceil and b>=floor]
  assert not complement(intervals,floor,ceil) and width<=eps
  if ws not in definitions:definitions[ws]=dict(label=('KF' if ws==('131',) else chr(65+sum(d['label']!='KF' for d in definitions.values()))),alphabet='123',forbidden=list(ws))
  entry=dict(claim=number,label=definitions[ws]['label'],forbidden=list(ws),left=left,right=right,target=row['target'],origin=row['origin'],
             dominance_bound=str(upper(left,right)),background_bound=str(bg),radius=4,tail_bound_iterations=16,prefix_relaxations=history,
             rational_leaf_check=dict(covered=[[str(a),str(b)] for a,b in intervals],maximum_width=str(width)),
             source_factors=[dict(left=s['left'],right=s['right']) for s in row['sources']])
  output.append(entry);print(number,entry['label'],len(ws),left,right,'upper',float(upper(left,right)),flush=True)
 assert not complement([tuple(Q(str(x)) for x in c['target']) for c in output],Q('4.1'),Q('4.52'))
 sources=['replacement_cover.json','simple_choices_refined.json','short_choices_refined.json','last_short_choices_refined.json']
 result=dict(status='Unproved inclusion candidates; rational full-target distance <=1e-9',definitions=list(definitions.values()),claims=output,
             source_sha256={s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources},
             construction='Use newly scanned simpler models; clip old row 8, insert KF+KF, merge shared models, and enlarge prefix factors only with exact cross-pair dominance.')
 (ROOT/'simple_cover.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
