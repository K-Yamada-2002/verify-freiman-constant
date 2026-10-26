"""Discovery only: below-ray roots joining Freiman's saved closed family.

Float screening cannot certify a result. Candidates are subsequently checked
by the independent exact verifier in this folder. Freiman files are read only.
"""
import sys, json, argparse, bisect
from pathlib import Path
from itertools import product
from functools import lru_cache
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'Freiman/src'))
from exact_cf import K, CF, interval, parameters, matrix, tail_endpoint
from obstruction_probe import scan
@lru_cache(None)
def tails(state):
 return tuple(float(tail_endpoint(state,v)) for v in (True,False))

def apply(word,x):
 a,b,c,d=matrix(word);return (a*x+b)/(c*x+d)

@lru_cache(None)
def word_info(word):
 state=scan(word)
 if state is None:return None
 a,b,c,d=matrix(word);vals=[apply(word,x) for x in tails(state)]
 return min(vals),max(vals),c/d,d,state

def maximum(word,state):return apply(word,tails(state)[len(word)%2==0])

def core_max(a,b,center):
 core=a[::-1]+(center,)+b;sa,sb=scan(a),scan(b)
 return max([0]+[d+maximum(core[:i][::-1],sa)+maximum(core[i+1:],sb)
                 for i,d in enumerate(core) if i!=len(a) and d>=3])
from endpoint_return import ReturnSearch


def main():
 p=argparse.ArgumentParser();p.add_argument('--length',type=int,default=6);p.add_argument('--limit',type=int,default=30);args=p.parse_args()
 lower,upper=4.5251,float(CF)
 words=[]
 for n in range(2,args.length+1):
  for rest in product((1,2,3),repeat=n-1):
   for d in (3,4):
    w=(d,)+rest
    if scan(w) is not None:words.append(w)
 aa=[w for w in words if w[0]==3];bb=sorted([w for w in words if w[0]==4],key=lambda w:word_info(w)[0]);lows=[word_info(w)[0] for w in bb]
 candidates=[]
 for a in aa:
  la,ha,*_=word_info(a)
  for b in bb[:bisect.bisect_right(lows,upper-4-la)]:
   lb,hb,*_=word_info(b)
   if ha+hb+4<lower:continue
   cm=core_max(a,b,4);lo=max(4+la+lb,cm,lower);hi=min(4+ha+hb,upper)
   if lo<hi:candidates.append((hi-lo,a,b,lo,hi,cm))
 print('screen candidates',len(candidates),flush=True)
 kernel=ReturnSearch('graph_wide');found=[]
 for _,a,b,lo,hi,cm in sorted(candidates,reverse=True):
  r,s,rho=parameters(a,b);x=tail_endpoint(scan(a),len(a)%2==0);y=tail_endpoint(scan(b),len(b)%2==0);z=(1+r*x)/(1+s*y);S=rho*z*z
  i=kernel.index(S)
  keys=[(len(scan(w)),len(w)%2,w[-kernel.memory:]) for w in (a,b)]
  if not kernel.low<=i<=kernel.high or any(k not in kernel.ids for k in keys):continue
  try:
   kernel.side(a,(),(r,r));kernel.side(b,(),(s,s))
  except AssertionError:continue
  g=kernel.ids[keys[0]]*kernel.sides+kernel.ids[keys[1]]
  L,H=interval(a,b)
  for typ,p,q in kernel.bands:
   if ((g*kernel.bins+i-kernel.low)*kernel.T+typ) not in kernel.alive:continue
   l,h=4+L+p*(H-L),4+L+q*(H-L)
   ll,hh=max(float(l),lo),min(float(h),hi)
   if ll<hh:
    row={'a':''.join(map(str,a)),'b':''.join(map(str,b)),'center':4,'band':[str(p),str(q)],'interval':[(l-4).data(),(h-4).data()],'proofs':[{'kernel':'graph_wide','geometry':g,'bin':i,'type':typ,'band':[str(p),str(q)]}],'screen':[ll,hh],'core_max':cm}
    found.append(row);print(json.dumps(row),flush=True)
    break
  if len(found)>=args.limit:break
 (ROOT/'Berstein/data/freiman_bridge_candidates.json').write_text(json.dumps({'proof_complete':False,'candidates':found},indent=2)+'\n')
if __name__=='__main__':main()
