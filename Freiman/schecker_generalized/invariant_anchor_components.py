#!/usr/bin/env python3
"""Floating component search using derivatives at extremal tail anchors.

The scale R=q*(1+r*alpha)^2/(1+s*beta)^2 is unchanged by simultaneous
six-digit periodic returns. Both choices of extremal anchors are allowed.
This remains a conservative discovery search, not an exact proof or an
exhaustive impossibility result. Includes ordinary steps of total length at
most two and one simultaneous extremal six-digit return on each side.
"""
import argparse,math,json
from functools import lru_cache
from pathlib import Path
import invariant_boxes as ib
from invariant_endpoint_components import ComponentSearch,pool,mapped_pool
from explore import matrix,state_of,extreme_tail,transform

@lru_cache(None)
def anchor(s,h):return extreme_tail(state_of(s),h)[0]
@lru_cache(None)
def anchor_float(s,h):return float(anchor(s,h).decimal())
@lru_cache(None)
def delta(s,h,x,y):
 if x==y:return 0.,0.
 z=anchor_float(s,h)
 a,b=2*z,z*z;c,d=x+y,x*y
 aa,bb,cc=b*c-a*d,2*(b-d),a-c
 pts=list(map(float,ib.RANGES[ib.STATES.index(s)]))
 if abs(aa)<1e-16:
  if abs(bb)>1e-16:
   root=-cc/bb
   if pts[0]<root<pts[1]:pts.append(root)
 elif bb*bb-4*aa*cc>=0:
  for root in ((-bb-math.sqrt(bb*bb-4*aa*cc))/(2*aa),(-bb+math.sqrt(bb*bb-4*aa*cc))/(2*aa)):
   if pts[0]<root<pts[1]:pts.append(root)
 vals=[(x-y)*(1+z*r)**2/((1+r*x)*(1+r*y)) for r in pts]
 return min(vals),max(vals)
@lru_cache(None)
def factor(s,h,u,hh):
 t=ib.suffix_state(s+u);a,b,c,d=matrix(u)
 old,new=anchor(s,h),anchor(t,hh)
 if transform(u,new)==old:
  z=float((c*new+d).decimal());return z,z
 old,new=map(lambda x:float(x.decimal()),(old,new))
 vals=[(r*(a*new+b)+c*new+d)/(1+r*old) for r in map(float,ib.RANGES[ib.STATES.index(s)])]
 return min(vals),max(vals)
@lru_cache(None)
def extreme_word(s,h):
 _,pre,period=extreme_tail(state_of(s),h)
 return (pre+period*2)[:6]

class Anchored(ComponentSearch):
 def __init__(self,bins=25,base=.88,max_step=2):
  self.qboxes=tuple((base**(i+1),base**i) for i in range(bins))
  self.ranges={s:tuple(map(float,r)) for s,r in zip(ib.STATES,ib.RANGES)}
  self.cells=[(s,t,p,qi,h) for s in ib.STATES for t in ib.STATES for p in (1,-1) for qi in range(bins) for h in (False,True)]
  self.index={c:i for i,c in enumerate(self.cells)}
  self.domains=[];self.offers=[];self.order=[]
  for cell in self.cells:
   s,t,p,qi,h=cell
   points=pool(s,t);order=sorted(range(len(points)),key=lambda i:self.value(cell,points[i]))
   self.order.append(order);self.domains.append(((order[0],order[-1]),))
   moves=[];suffixes=list(ib.suffix_pairs(s,t,max_step))
   suffixes.append((extreme_word(s,h),extreme_word(t,h if p>0 else not h)))
   for u,v in suffixes:
    for childh in (False,True):
     deps=self.dependencies(cell,u,v,childh)
     if deps:moves.append((u,v,deps,mapped_pool(s,t,u,v)))
   self.offers.append(moves)
 def value(self,cell,z):
  s,t,p,qi,h=cell;r=sum(self.ranges[s])/2;ss=sum(self.ranges[t])/2;q=sum(self.qboxes[qi])/2
  x,y=z;a=anchor_float(s,h);b=anchor_float(t,h if p>0 else not h)
  return (1+r*a)**2*x/(1+r*x)+p*q*(1+ss*b)**2*y/(1+ss*y)
 def ge(self,cell,a,b):
  if a==b:return True
  s,t,p,qi,h=cell
  dl=delta(s,h,a[0],b[0])[0]
  dr=delta(t,h if p>0 else not h,a[1],b[1]);dr=dr[0] if p>0 else -dr[1]
  return dl+self.qboxes[qi][0 if dr>=0 else 1]*dr>=-1e-12
 def dependencies(self,cell,u,v,childh):
  s,t,p,qi,h=cell;pp=p*(-1)**(len(u)+len(v));ss,tt=ib.suffix_state(s+u),ib.suffix_state(t+v)
  a,b=factor(s,h,u,childh);c,d=factor(t,h if p>0 else not h,v,childh if pp>0 else not childh)
  lo,hi=self.qboxes[qi][0]*(a/d)**2,self.qboxes[qi][1]*(b/c)**2
  if lo<self.qboxes[-1][0]-1e-12 or hi>1/self.qboxes[-1][0]+1e-12:return None
  ranges=[]
  if lo<1:ranges.append((ss,tt,lo,min(hi,1),False,childh))
  if hi>1:ranges.append((tt,ss,1/hi,min(1/lo,1),True,childh if pp>0 else not childh))
  out=[]
  for aa,bb,l,h,swap,ch in ranges:
   mapping={z:i for i,z in enumerate(pool(aa,bb))}
   ids=tuple(mapping[z[::-1] if swap else z] for z in pool(ss,tt))
   for j,(low,high) in enumerate(self.qboxes):
    if max(low,l)<min(high,h)-1e-12:out.append((self.index[aa,bb,pp,j,ch],ids))
  return tuple(out)

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--bins',type=int,default=25)
 ap.add_argument('--base',type=float,default=.88)
 ap.add_argument('--rounds',type=int,default=50)
 ap.add_argument('--output',type=Path)
 args=ap.parse_args()
 search=Anchored(args.bins,args.base);print('prepared',len(search.cells),flush=True)
 result=search.run(args.rounds)
 result['ratio_parameter']='derivative ratio at the chosen extremal tail anchors'
 result['settings']={'bins':args.bins,'base':args.base,'rounds':args.rounds,
                     'states':6,'max_step':2,'simultaneous_extremal_return':6}
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
