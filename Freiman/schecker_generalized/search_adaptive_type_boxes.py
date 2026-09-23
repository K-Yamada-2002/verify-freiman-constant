#!/usr/bin/env python3
"""Try a closed parameter-box system using endpoint types learned adaptively.

This is floating discovery, distinct from the exact finite certificate that
supplies the type bank. A nonempty survivor graph still requires exact replay.
"""
import argparse
import json
from pathlib import Path

import invariant_boxes as ib
from adaptive_induction import verify
from adaptive_types import word_pair


class CachedBoxSearch(ib.BoxSearch):
    """Avoid repeatedly hashing large quadratic-field fractions in discovery."""
    def __init__(self,*args):
        self._float_cache={};self._cell=None;self._comparisons={}
        super().__init__(*args)

    def values(self,pair):
        key=id(pair)
        if key not in self._float_cache:
            # Retain the pair as well, so the object id cannot be recycled.
            self._float_cache[key]=(pair,tuple(float(z.decimal()) for z in pair))
        return self._float_cache[key][1]

    def ge(self,a,b,rb,sb,qb,p,si,ti):
        cell=(rb,sb,qb,p)
        if cell!=self._cell:
            self._cell=cell;self._comparisons={}
            self._bounds=tuple(tuple(map(float,z)) for z in (rb,sb,qb))
        key=id(a),id(b)
        if key in self._comparisons:return self._comparisons[key]
        aa,bb=self.values(a),self.values(b)
        if aa==bb:result=a==b
        else:
            x,y=aa;xx,yy=bb;dr,ds=x-xx,p*(y-yy)
            rbox,sbox,qbox=self._bounds
            r=rbox[1 if dr>=0 else 0];s=sbox[1 if ds>=0 else 0];q=qbox[0 if ds>=0 else 1]
            result=dr/((1+r*x)*(1+r*xx))+q*ds/((1+s*y)*(1+s*yy))>1e-12
        self._comparisons[key]=result
        return result

    def prepare(self):
        # Intersect the available kinds once per transition, instead of
        # scanning all q bins separately for every kind.
        indexed={cell:{self.nodes[n][1]:n for n in self.proof[cid]}
                 for cid,cell in enumerate(self.cells)}
        lower=float(self.qboxes[-1][0])
        for si,ti,p,qi in self.cells:
            s,t=ib.STATES[si],ib.STATES[ti]
            rb,sb,qb=ib.RANGES[si],ib.RANGES[ti],self.qboxes[qi]
            row=[]
            for u,v in ib.suffix_pairs(s,t,self.max_step):
                ss,tt=ib.suffix_state(s+u),ib.suffix_state(t+v)
                a,b=ib.STATES.index(ss),ib.STATES.index(tt)
                lo,hi=self.image_range(s,t,p,u,v,rb,sb,qb)
                if lo<lower-1e-14 or hi>1/lower+1e-14:continue
                pp=p*(-1)**(len(u)+len(v))
                ranges=[]
                if lo<=1:ranges.append((a,b,lo,min(hi,1.),False))
                if hi>=1:ranges.append((b,a,1/hi,min(1/lo,1.),True))
                mappings=[]
                for aa,bb,l,h,swap in ranges:
                    for qj,(qlo,qhi) in enumerate(self.qboxes):
                        if float(qlo)>h+1e-13 or float(qhi)<l-1e-13:continue
                        kinds=indexed[aa,bb,pp,qj]
                        mappings.append({ib.type_reflect(k) if swap else k:n for k,n in kinds.items()})
                if not mappings:continue
                kinds=set(mappings[0])
                for mapping in mappings[1:]:kinds.intersection_update(mapping)
                for kind in sorted(kinds):
                    ep=ib.endpoints(s,t,p,kind,u,v)
                    if ep is None:continue
                    if self.ge(ep[1],ep[0],rb,sb,qb,p,si,ti):pass
                    elif self.ge(ep[0],ep[1],rb,sb,qb,p,si,ti):ep=ep[::-1]
                    else:continue
                    row.append({'suffixes':(u,v),'kind':kind,
                                'dependencies':tuple(sorted({m[kind] for m in mappings})),
                                'endpoints':ep,'upper_mid':self.point(ep[1],rb,sb,qb,p,si,ti)})
            self.offers.append(row)

    def cover(self,cid,parent,offers):
        # Many endpoint types share a boundary. Cache the next greedy step
        # for that boundary within this cell and elimination round.
        if getattr(self,'_active_offers',None) is not offers:
            self._active_offers=offers
            self._sorted_offers=sorted(offers,key=lambda item:item[1]['upper_mid'],reverse=True)
            self._next_steps={}
        si,ti,p,qi=self.cells[cid]
        rb,sb,qb=ib.RANGES[si],ib.RANGES[ti],self.qboxes[qi]
        current=parent[0];used=[];last_mid=-float('inf')
        while not self.ge(current,parent[1],rb,sb,qb,p,si,ti):
            key=id(current),last_mid
            if key not in self._next_steps:
                best=None
                for j,o in self._sorted_offers:
                    if o['upper_mid']<=last_mid+1e-13:break
                    if (self.ge(o['endpoints'][1],current,rb,sb,qb,p,si,ti)
                            and self.ge(current,o['endpoints'][0],rb,sb,qb,p,si,ti)):
                        best=j,o;break
                self._next_steps[key]=best
            best=self._next_steps[key]
            if best is None:return None
            j,o=best;used.append(j);current=o['endpoints'][1];last_mid=o['upper_mid']
        return used


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--max-step',type=int,choices=(1,2),default=1)
    ap.add_argument('--bins',type=int,default=17)
    ap.add_argument('--base',default='5/6',help='rational multiplicative q-bin spacing')
    ap.add_argument('--states',type=int,choices=(6,13),default=6)
    ap.add_argument('--observed-types-only',action='store_true',
                    help='restrict shapes at each state/parity to occurrences in the certificate')
    ap.add_argument('--rounds',type=int,default=30)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    source=json.loads(args.certificate.read_text());verify(source)
    assert 'cases' not in source,'use one parameter case as the discovery source'
    if args.states==13:ib.STATES,ib.RANGES=ib.STATES13,ib.RANGES13
    used=sorted({n['type'][0] for n in source['nodes']})
    shapes=[tuple(tuple(z) for z in source['types'][i]) for i in used]
    reflected=lambda pair:tuple(z[2:]+z[:2] for z in pair)
    labels=(None,)+tuple(p for shape in shapes for p in (shape,reflected(shape)))
    ib.TYPE_LABELS=ib.ALL_TYPE_LABELS=labels
    ib.endpoints.cache_clear()
    if args.observed_types_only:
        from functools import lru_cache
        observed={};shape_index={old:i for i,old in enumerate(used)}
        for node in source['nodes']:
            left,right=word_pair(node['left_suffix'],node['right_suffix'])
            s,t=ib.suffix_state(left),ib.suffix_state(right)
            assert s is not None and t is not None
            p=(-1)**(len(left)+len(right))
            kind=1+2*shape_index[node['type'][0]]+int(node['type'][1])
            observed.setdefault((s,t,p),set()).add(kind)
            observed.setdefault((t,s,p),set()).add(ib.type_reflect(kind))
        original=ib.endpoints
        @lru_cache(None)
        def limited(s,t,p,kind,u='',v=''):
            cell=(ib.suffix_state(s+u),ib.suffix_state(t+v),p*(-1)**(len(u)+len(v)))
            if kind not in observed.get(cell,()):return None
            return original(s,t,p,kind,u,v)
        ib.endpoints=limited
    search=CachedBoxSearch(args.bins,args.max_step,ib.F(args.base))
    print('prepared',len(shapes),'learned shapes',len(search.nodes),'nodes',
          sum(map(len,search.offers)),'offers',flush=True)
    alive,plans,history=search.run(args.rounds)
    data=search.save(alive,plans,history)
    data['fixed_point_reached']=data['closed']
    data['closed']=bool(alive) and data['closed']
    data['source_certificate']=str(args.certificate)
    data['q_base']=args.base
    data['observed_types_only']=args.observed_types_only
    data['type_labels']=labels
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')
    print('nonempty closed candidate',data['closed'],'survivors',len(alive),flush=True)


if __name__=='__main__':main()
