"""Exact universal-cover predicates for resettable T2/F parameter boxes."""
from functools import lru_cache
from collections import deque
from typed_intervals import cf,endpoints,channels
from obstruction_probe import scan,step


@lru_cache(None)
def side_pairs(state,parity,word,lang):
    for d in word:
        state=step(state,d)
        if state is None:raise ValueError('Forbidden child')
    values=sorted(cf(word,t) for t in endpoints(state,lang))
    return tuple(values if not parity else reversed(values))


@lru_cache(None)
def pairs(a,b,u,w,kind):
    out=[]
    for ka,kb in channels(kind):
        aa=side_pairs(scan(a),len(a)%2,u,ka);bb=side_pairs(scan(b),len(b)%2,w,kb)
        out.append(((aa[0],bb[0]),(aa[1],bb[1])))
    return tuple(out)


def lower_difference(x,y,box,pa,pb):
    aa=[(-1)**pa*(x[0]/(1+r*x[0])-y[0]/(1+r*y[0])) for r in box[0]]
    bb=[rho*(-1)**pb*(x[1]/(1+s*x[1])-y[1]/(1+s*y[1])) for s in box[1] for rho in box[2]]
    return min(aa)+min(bb)


class Uniform:
    def __init__(self,a,b,kind,box):
        self.a=a;self.b=b;self.kind=kind;self.box=box
        self.parent=pairs(a,b,(),(),kind)
        self.cache={};self.checks=0
    def ge(self,x,y):
        key=x,y
        if key not in self.cache:
            self.checks+=1
            self.cache[key]=lower_difference(x,y,self.box,len(self.a)%2,len(self.b)%2)>=0
        return self.cache[key]
    def get(self,vertex):return pairs(self.a,self.b,*vertex)
    def left_anchor(self,v):
        child=self.get(v)
        return all(any(self.ge(p[0],c[0]) for c in child) for p in self.parent)
    def right_anchor(self,v):
        child=self.get(v)
        return all(any(self.ge(c[1],p[1]) for c in child) for p in self.parent)
    def overlap(self,u,v):
        aa,bb=self.get(u),self.get(v)
        return (any(self.ge(x[1],y[0]) for x in aa for y in bb)
                and any(self.ge(y[1],x[0]) for x in aa for y in bb))
    def verify(self,menu):
        return (bool(menu) and any(self.left_anchor(v) for v in menu)
                and any(self.right_anchor(v) for v in menu)
                and all(self.overlap(u,v) for u,v in zip(menu,menu[1:])))
    def select(self,candidates):
        # Any path between the two sets of anchors is a connected covering chain.
        vertices=[(u,w,t) for _,_,u,w,t in candidates]
        numeric=[(lo,hi) for lo,hi,*_ in candidates]
        queue=deque();pred={}
        for i,v in enumerate(vertices):
            if self.left_anchor(v):queue.append(i);pred[i]=None
        while queue:
            i=queue.popleft();v=vertices[i]
            if self.right_anchor(v):
                chain=[]
                while i is not None:chain.append(vertices[i]);i=pred[i]
                chain.reverse();assert self.verify(chain);return chain
            choices=[j for j in range(len(vertices)) if j not in pred
                     and numeric[j][0]<=numeric[i][1]+1e-12
                     and numeric[i][0]<=numeric[j][1]+1e-12]
            choices.sort(key=lambda j:numeric[j][1],reverse=True)
            for j in choices:
                if self.overlap(v,vertices[j]):pred[j]=i;queue.append(j)
        return None
