#!/usr/bin/env python3
"""Search a closed interval-type system on six suffix states and q boxes.

Discovery is floating point; a surviving system must be replayed exactly.
The parameter r boxes are preserved by legal digit transitions. Reflections
normalize q to <=1. A child is usable only if its whole parameter image is
covered by retained boxes of the required type.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
from explore import Q, state_of, extreme_tail, transform, matrix
from search_shape_bank import SHAPES,SHAPES8,reflect

STATES=('1','2','3','31','313','3131')
RANGES=((F(5,9),F(4,5)),(F(5,14),F(4,9)),(F(5,19),F(4,13)),
        (F(13,17),F(19,24)),(F(24,91),F(17,64)),(F(64,81),F(91,115)))
TYPE_LABELS=(None,)+tuple(label for shape in SHAPES for label in (shape,tuple(map(reflect,shape))))
ALL_TYPE_LABELS=(None,)+tuple(label for shape in SHAPES8 for label in (shape,tuple(map(reflect,shape))))
STATES13=('11','21','12','22','32','13','23','33','131','231','331','313','3131')
RANGES13=((F(5,9),F(9,14)),(F(9,13),F(14,19)),(F(5,14),F(9,23)),
          (F(9,22),F(14,33)),(F(13,30),F(19,43)),(F(5,19),F(9,32)),
          (F(9,31),F(14,47)),(F(13,43),F(19,62)),(F(32,41),F(19,24)),
          (F(47,61),F(31,40)),(F(62,81),F(43,56)),
          (F(24,91),F(17,64)),(F(64,81),F(91,115)))


def suffix_state(word):
    if '31313' in word:return None
    return max((s for s in STATES if word.endswith(s)),key=len)


def type_reflect(kind):return 0 if not kind else (kind+1 if kind%2 else kind-1)


@lru_cache(None)
def tail_endpoint(state,suffix,high):
    if '31313' in state+suffix:return None
    return transform(suffix,extreme_tail(state_of(state+suffix),high)[0])


@lru_cache(None)
def endpoints(s,t,p,kind,u='',v=''):
    """Exact pairs of tail values, before applying the parent's Mobius maps."""
    ss=suffix_state(s+u);tt=suffix_state(t+v)
    if ss is None or tt is None:return None
    parity=p*(-1)**(len(u)+len(v))
    if kind==0:
        labels=(('',False,'',parity<0),('',True,'',parity>0))
    else:labels=ALL_TYPE_LABELS[kind]
    result=[]
    for a,high_a,b,high_b in labels:
        x=tail_endpoint(s,u+a,high_a);y=tail_endpoint(t,v+b,high_b)
        if x is None or y is None:return None
        result.append((x,y))
    return tuple(result)


@lru_cache(None)
def floats(pair):return tuple(float(x.decimal()) for x in pair)


def minimum_difference(a,b,rbox,sbox,qbox,p,exact=False):
    """Exact minimum over the rectangle of F(a)-F(b).

    Differences G_r(x)-G_r(y) have a constant sign and are monotone in r.
    Hence independently choosing the proper r,s,q endpoints is exact.
    """
    if exact:
        x,y=a;xx,yy=b
    else:
        x,y=floats(a);xx,yy=floats(b)
        rbox=tuple(map(float,rbox));sbox=tuple(map(float,sbox));qbox=tuple(map(float,qbox))
    dr=x-xx;ds=p*(y-yy)
    r=rbox[1] if dr>=0 else rbox[0]
    s=sbox[1] if ds>=0 else sbox[0]
    q=qbox[0] if ds>=0 else qbox[1]
    return dr/((1+r*x)*(1+r*xx))+q*ds/((1+s*y)*(1+s*yy))


def positive_or_identity(a,b,rbox,sbox,qbox,p):
    return a==b or minimum_difference(a,b,rbox,sbox,qbox,p)>1e-12


@lru_cache(None)
def suffix_pairs(s,t,max_step):
    out=[]
    for total in range(1,max_step+1):
        for i in range(total+1):
            for aa in product('123',repeat=i):
                u=''.join(aa)
                if suffix_state(s+u) is None:continue
                for bb in product('123',repeat=total-i):
                    v=''.join(bb)
                    if suffix_state(t+v) is not None:out.append((u,v))
    return tuple(out)


class BoxSearch:
    def __init__(self,bins=17,max_step=2):
        self.qboxes=tuple((F(5,6)**(i+1),F(5,6)**i) for i in range(bins))
        self.max_step=max_step;self.cells=[];self.lookup={};self.nodes=[]
        self.proof={};self.offers=[]
        for si,s in enumerate(STATES):
            for ti,t in enumerate(STATES):
                for p in (1,-1):
                    for qi,qbox in enumerate(self.qboxes):
                        cid=len(self.cells)
                        self.cells.append((si,ti,p,qi));parents=[]
                        for kind in range(len(TYPE_LABELS)):
                            ep=endpoints(s,t,p,kind)
                            if ep is None:continue
                            rbox,sbox=RANGES[si],RANGES[ti]
                            # Ordering is required to be uniform on this cell.
                            if self.ge(ep[1],ep[0],rbox,sbox,qbox,p,si,ti):pass
                            elif self.ge(ep[0],ep[1],rbox,sbox,qbox,p,si,ti):ep=ep[::-1]
                            else:continue
                            if ep[0]==ep[1]:continue
                            nid=len(self.nodes)
                            self.nodes.append((cid,kind,ep));self.lookup[(si,ti,p,qi,kind)]=nid
                            parents.append(nid)
                        self.proof[cid]=parents
        self.prepare()

    def ge(self,a,b,rb,sb,qb,p,si,ti):
        return positive_or_identity(a,b,rb,sb,qb,p)

    def point(self,pair,rb,sb,qb,p,si,ti):
        r,s,q=map(lambda z:float(sum(z)/2),(rb,sb,qb))
        x,y=floats(pair);return x/(1+r*x)+p*q*y/(1+s*y)

    def image_range(self,s,t,p,u,v,rb,sb,qb):
        aa,bb,cc,dd=matrix(u);a,b,c,d=matrix(v)
        lo=float(qb[0]*(rb[0]*bb+dd)**2/(sb[1]*b+d)**2)
        hi=float(qb[1]*(rb[1]*bb+dd)**2/(sb[0]*b+d)**2)
        return lo,hi

    def dependencies(self,si,ti,p,lo,hi,kind):
        # q is a denominator-scale parameter. Swap sides for q>1.
        if lo<float(self.qboxes[-1][0])-1e-14 or hi>1/float(self.qboxes[-1][0])+1e-14:return None
        ranges=[]
        if lo<=1:ranges.append((si,ti,kind,lo,min(hi,1.0)))
        if hi>=1:ranges.append((ti,si,type_reflect(kind),1/hi,min(1/lo,1.0)))
        result=set()
        for a,b,k,l,h in ranges:
            for qi,(qlo,qhi) in enumerate(self.qboxes):
                if float(qlo)>h+1e-13 or float(qhi)<l-1e-13:continue
                node=self.lookup.get((a,b,p,qi,k))
                if node is None:return None
                result.add(node)
        return tuple(sorted(result))

    def prepare(self):
        for cid,(si,ti,p,qi) in enumerate(self.cells):
            s,t=STATES[si],STATES[ti]
            rb,sb,qb=RANGES[si],RANGES[ti],self.qboxes[qi]
            rm,sm,qm=map(lambda z:float(sum(z)/2),(rb,sb,qb))
            row=[]
            for u,v in suffix_pairs(s,t,self.max_step):
                ss,tt=suffix_state(s+u),suffix_state(t+v)
                qlo,qhi=self.image_range(s,t,p,u,v,rb,sb,qb)
                pp=p*(-1)**(len(u)+len(v))
                for kind in range(len(TYPE_LABELS)):
                    deps=self.dependencies(STATES.index(ss),STATES.index(tt),pp,qlo,qhi,kind)
                    if deps is None:continue
                    ep=endpoints(s,t,p,kind,u,v)
                    if ep is None:continue
                    if self.ge(ep[1],ep[0],rb,sb,qb,p,si,ti):pass
                    elif self.ge(ep[0],ep[1],rb,sb,qb,p,si,ti):ep=ep[::-1]
                    else:continue
                    row.append({'suffixes':(u,v),'kind':kind,'dependencies':deps,
                                'endpoints':ep,'upper_mid':self.point(ep[1],rb,sb,qb,p,si,ti)})
            self.offers.append(row)

    def cover(self,cid,parent,offers):
        si,ti,p,qi=self.cells[cid]
        rb,sb,qb=RANGES[si],RANGES[ti],self.qboxes[qi]
        current=parent[0];used=[];last_mid=-float('inf')
        while not self.ge(current,parent[1],rb,sb,qb,p,si,ti):
            best=None
            for j,o in offers:
                if o['upper_mid']<=last_mid+1e-13:continue
                if not self.ge(o['endpoints'][1],current,rb,sb,qb,p,si,ti):continue
                if self.ge(current,o['endpoints'][0],rb,sb,qb,p,si,ti):
                    if best is None or o['upper_mid']>best[1]['upper_mid']:best=j,o
            if best is None:return None
            j,o=best;used.append(j);current=o['endpoints'][1];last_mid=o['upper_mid']
        return used

    def run(self,rounds=30):
        alive=set(range(len(self.nodes)));history=[];plans={}
        for iteration in range(rounds):
            removed=[];newplans={}
            for cid,parents in self.proof.items():
                active=[n for n in parents if n in alive]
                if not active:continue
                offers=[(j,o) for j,o in enumerate(self.offers[cid])
                        if all(k in alive for k in o['dependencies'])]
                for n in active:
                    chain=self.cover(cid,self.nodes[n][2],offers)
                    if chain is None:removed.append(n)
                    else:newplans[n]=chain
            history.append({'round':iteration,'alive_before':len(alive),'removed':len(removed)})
            print(history[-1],flush=True)
            alive.difference_update(removed);plans=newplans
            if not removed:break
        return alive,plans,history

    def save(self,alive,plans,history):
        rows=[]
        for n in sorted(alive):
            cid,kind,ep=self.nodes[n];si,ti,p,qi=self.cells[cid]
            rows.append({'id':n,'states':[STATES[si],STATES[ti]],'parity':p,
                         'q_box':[str(x) for x in self.qboxes[qi]],'kind':kind,
                         'children':[{'suffixes':self.offers[cid][j]['suffixes'],
                                      'kind':self.offers[cid][j]['kind'],
                                      'dependencies':self.offers[cid][j]['dependencies']}
                                     for j in plans.get(n,[])]})
        return {'status':'floating-point box-invariant search; requires exact verification',
                'max_step':self.max_step,'q_bins':len(self.qboxes),'history':history,
                'state_ranges':{s:[str(x) for x in r] for s,r in zip(STATES,RANGES)},
                'closed':bool(history and not history[-1]['removed']),'survivors':rows}


def main():
    global STATES,RANGES
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--bins',type=int,default=17)
    ap.add_argument('--max-step',type=int,default=2)
    ap.add_argument('--rounds',type=int,default=30)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--states',type=int,choices=(6,13),default=6)
    args=ap.parse_args()
    if args.states==13:STATES,RANGES=STATES13,RANGES13
    for s,(lo,hi) in zip(STATES,RANGES):
        for digit in '123':
            t=suffix_state(s+digit)
            if t is not None:
                tlo,thi=RANGES[STATES.index(t)]
                assert tlo<=1/(int(digit)+hi)<=1/(int(digit)+lo)<=thi
    search=BoxSearch(args.bins,args.max_step)
    print('prepared',len(search.nodes),'nodes',sum(map(len,search.offers)),'offers',flush=True)
    alive,plans,history=search.run(args.rounds)
    data=search.save(alive,plans,history)
    print('survivors',len(alive),'closed',data['closed'],flush=True)
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
