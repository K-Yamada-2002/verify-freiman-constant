"""Lazy finite-cell search with parent replanning after child-cell rejection.

Rejected means unusable by this finite search, not mathematically impossible.
Every retained row has a uniform exact local-cover certificate. Only a closed
reachable component containing the requested root is a proof certificate.
"""
import argparse
import json
import math
import time
from fractions import Fraction as Q
from collections import deque,defaultdict,Counter
from pathlib import Path
from layout import DATA
from obstruction_probe import scan,STATES
from exact_cf import parameters
from box_certificates import suffix_range,child_box,contains,encode_box
from typed_boxes import Uniform


class Catalog:
    def __init__(self,memory=3,base=Q(21,20),length=12,nodes=3000,lookahead=3,limit=100,pure_t2=True,types=('T2','F')):
        self.memory=memory;self.base=base;self.length=length;self.nodes=nodes;self.lookahead=lookahead;self.limit=limit
        self.pure_t2=pure_t2
        self.types=types
        self.pow={};self.boxes={};self.prototypes={};self.states={};self.rows={};self.reverse=defaultdict(set)
        self.queue=deque();self.queued=set();self.events=[]
    def power(self,i):
        if i not in self.pow:self.pow[i]=self.base**i
        return self.pow[i]
    def index(self,rho):
        i=math.floor(math.log(float(rho))/math.log(float(self.base)))
        while rho<self.power(i):i-=1
        while rho>=self.power(i+1):i+=1
        return i
    def key(self,a,b,kind,index):
        return (len(scan(a)),len(scan(b)),len(a)%2,len(b)%2,a[-self.memory:],b[-self.memory:],index,kind)
    def prototype(self,key):
        if key in self.prototypes:return self.prototypes[key]
        def one(st,parity,suffix):
            word=STATES[st] if len(STATES[st])>len(suffix) else suffix
            if len(word)%2!=parity:word=(2,)+word
            assert scan(word)==STATES[st] and word[-self.memory:]==suffix
            return word
        a=one(key[0],key[2],key[4]);b=one(key[1],key[3],key[5])
        self.prototypes[key]=a,b;return a,b
    def box(self,key):
        if key not in self.boxes:
            a,b=self.prototype(key)
            r=suffix_range(a,max(self.memory,key[0]));s=suffix_range(b,max(self.memory,key[1]))
            self.boxes[key]=(r,s,(self.power(key[6]),self.power(key[6]+1)))
        return self.boxes[key]
    def schedule(self,key,urgent=False):
        if key in self.queued:
            if not urgent:return
            self.queue.remove(key)
        else:self.queued.add(key)
        if urgent:self.queue.appendleft(key)
        else:self.queue.append(key)
    def child_keys(self,parent,u,w,typ):
        a,b=self.prototype(parent);mapped=child_box(self.box(parent),u,w)
        if mapped[2][0]<Q(1,self.limit) or mapped[2][1]>self.limit:return None
        lower,upper=self.index(mapped[2][0]),self.index(mapped[2][1])
        if mapped[2][1]==self.power(upper):upper-=1
        keys=[self.key(a+u,b+w,typ,i) for i in range(lower,upper+1)]
        for key in keys:
            box=self.box(key)
            assert contains(box[:2],mapped[:2]),(parent,key,box,mapped)
        assert self.power(lower)<=mapped[2][0] and mapped[2][1]<=self.power(upper+1)
        return keys
    def coordinates(self,a,b):return parameters(a,b)
    def search_params(self,key,box):return tuple((lo+hi)/2 for lo,hi in box)
    def uniform(self,key):
        a,b=self.prototype(key);return Uniform(a,b,key[-1],self.box(key))
    def process(self,key):
        a,b=self.prototype(key);box=self.box(key);mid=self.search_params(key,box)
        uniform=self.uniform(key);mapping={}
        def childmap(u,w,t):
            v=(u,w,t)
            if v not in mapping:mapping[v]=self.child_keys(key,u,w,t)
            return mapping[v]
        def guard(u,w,t):
            keys=childmap(u,w,t)
            return keys is not None and all(self.states.get(k)!='rejected' for k in keys)
        # Numerical search is optional; exact replay imports this module too.
        from typed_search import search
        result=search(a,b,key[-1],self.length,self.lookahead,self.limit,self.nodes,
                      params=mid,candidate_guard=guard,menu_selector=uniform.select,
                      allowed_types=('T2',) if self.pure_t2 and key[-1]=='T2' else self.types)
        old=self.rows.get(key)
        if old:
            for c in old['children']:self.reverse[c].discard(key)
        if result['status']=='exact_local_cover':
            menu=[(tuple(u),tuple(w),t) for u,w,t in result['menu']]
            assert uniform.verify(menu)
            children=set(c for u,w,t in menu for c in childmap(u,w,t))
            self.rows[key]={'menu':menu,'children':children,'counts':result['counts'],
                            'uniform_comparisons':uniform.checks}
            self.states[key]='certified_local'
            for child in sorted(children):
                self.reverse[child].add(key)
                if child not in self.states:self.states[child]='pending'
                if self.states[child]=='pending':self.schedule(child)
        else:
            self.states[key]='rejected';self.rows.pop(key,None)
            for parent in sorted(self.reverse[key]):
                if self.states.get(parent)!='rejected':self.schedule(parent,urgent=True)
        return result['status'],uniform.checks
    def reachable(self,root):
        seen=set();queue=[root]
        while queue:
            key=queue.pop()
            if key in seen:continue
            seen.add(key)
            if key in self.rows:queue.extend(self.rows[key]['children'])
        return seen
    def run(self,a,b,kind,max_steps=500,max_seconds=None):
        root=self.key(a,b,kind,self.index(self.coordinates(a,b)[2]))
        point=tuple((x,x) for x in self.coordinates(a,b));assert contains(self.box(root),point)
        self.states[root]='pending';self.schedule(root);start=time.monotonic()
        for iteration in range(max_steps):
            if max_seconds is not None and time.monotonic()-start>=max_seconds:break
            if not self.queue or self.states.get(root)=='rejected':break
            key=self.queue.popleft();self.queued.discard(key)
            # Previously selected menus may have become unreachable after replanning.
            if key not in self.reachable(root):continue
            status,checks=self.process(key)
            event={'step':iteration,'cell':repr(key),'result':status,'comparisons':checks,
                   'states':dict(Counter(self.states.values())),'pending':len(self.queue),
                   'seconds':time.monotonic()-start}
            self.events.append(event);print(json.dumps(event),flush=True)
        active=self.reachable(root)
        complete=all(self.states.get(k)=='certified_local' for k in active)
        ids={k:i for i,k in enumerate(sorted(self.states))}
        rows=[]
        for k in sorted(self.rows):
            row=self.rows[k];aa,bb=self.prototype(k)
            rows.append({'id':ids[k],'key':k,'prototype':[aa,bb],'box':encode_box(self.box(k)),
                         'menu':row['menu'],'children':[ids[c] for c in sorted(row['children'])],
                         'uniform_comparisons':row['uniform_comparisons']})
        return {'proof_complete':complete,'scope':'Typed auxiliary-interval covering lemma for the requested root only.',
                'settings':{'memory':self.memory,'base':str(self.base),'length':self.length,
                            'nodes':self.nodes,'lookahead':self.lookahead,'ratio_limit':self.limit,
                            'types':self.types,'pure_t2':self.pure_t2,
                            'max_seconds':max_seconds},
                'root':[list(a),list(b),kind],'root_cell':ids[root],'root_state':self.states[root],
                'rows':rows,'states':{str(ids[k]):v for k,v in self.states.items()},
                'cells':{str(ids[k]):k for k in self.states},
                'reachable':[ids[k] for k in sorted(active)],'events':self.events}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--left',default='32113');p.add_argument('--right',default='4322')
    p.add_argument('--type',default='F');p.add_argument('--memory',type=int,default=3)
    p.add_argument('--base',default='21/20');p.add_argument('--length',type=int,default=12)
    p.add_argument('--nodes',type=int,default=1500);p.add_argument('--lookahead',type=int,default=3)
    p.add_argument('--steps',type=int,default=500);p.add_argument('--output',default='typed_catalog.json')
    p.add_argument('--mixed-t2',action='store_true')
    args=p.parse_args();catalog=Catalog(args.memory,Q(args.base),args.length,args.nodes,args.lookahead,pure_t2=not args.mixed_t2)
    result=catalog.run(tuple(map(int,args.left)),tuple(map(int,args.right)),args.type,args.steps)
    result['settings']['pure_t2']=not args.mixed_t2
    (DATA/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'proof_complete':result['proof_complete'],'root_state':result['root_state'],
                      'rows':len(result['rows']),'reachable':len(result['reachable'])}),flush=True)
