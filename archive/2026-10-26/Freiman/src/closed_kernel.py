"""Exact reachable closure search inside a numerically discovered finite kernel.

Only a closed reachable graph is a success. Numerical kernel membership is
just a candidate filter; all retained menus and all child box inclusions are
recomputed with exact arithmetic. Intermediate kernel snapshots are allowed:
they cannot bypass the final exact closure requirement.
"""
import argparse,json,time
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
from functools import lru_cache
from typed_catalog import Catalog
from anchor_boxes import AnchorUniform,anchor,derivative_fraction
from obstruction_probe import scan,extremal_tail
from exact_cf import parameters
from box_certificates import child_box,contains,suffix_range

BASE=DATA


class ClosedKernel(Catalog):
    def __init__(self,name,group=1):
        self.meta=json.loads((BASE/(name+'.meta.json')).read_text())
        m=self.meta;assert m['coordinate']=='lower_endpoint_derivative_ratio'
        super().__init__(memory=m['memory'],base=Q(m['base']),pure_t2=False,types=tuple(m['types']))
        self.low,self.high=m['low'],m['high'];self.B=self.high-self.low+1
        self.side_ids={(q,p,tuple(s)):i for i,(q,p,s) in enumerate(m['side_keys'])}
        self.S=len(self.side_ids);self.T=len(self.types);self.type_ids={t:i for i,t in enumerate(self.types)}
        completed=BASE/(name+'.json')
        if completed.exists():
            result=json.loads(completed.read_text());self.allowed=set(result['alive']);self.source_fixed_point=True
        else:
            bits=(BASE/(name+'.json.alive.bin')).read_bytes()
            assert len(bits)==self.S*self.S*self.B*self.T
            self.allowed={i for i,v in enumerate(bits) if v};self.source_fixed_point=False
        self.exts=list(map(tuple,m['extensions']));self.ps=m['successor_pairs']
        self.group=group;self.charts={};self.ends={}
        for geom in range(self.S*self.S):
            for typ in range(self.T):
                run=[]
                def flush():
                    if not run:return
                    lo,hi=run[0],run[-1]
                    for i in run:self.charts[geom,typ,i]=lo
                    self.ends[geom,typ,lo]=hi
                    run.clear()
                for i in range(self.low,self.high+1):
                    if ((geom*self.B+i-self.low)*self.T+typ) in self.allowed:
                        if run and (len(run)>=group or i!=run[-1]+1):flush()
                        run.append(i)
                    else:flush()
                flush()
    def geometry(self,key):
        la=self.side_ids[(key[0],key[2],key[4])];lb=self.side_ids[(key[1],key[3],key[5])]
        return la*self.S+lb
    def key(self,a,b,kind,index):
        k=super().key(a,b,kind,index);g=self.geometry(k);t=self.type_ids[kind]
        start=self.charts.get((g,t,index))
        return None if start is None else k[:6]+(start,kind)
    def box(self,key):
        if key not in self.boxes:
            a,b=self.prototype(key);end=self.ends[self.geometry(key),self.type_ids[key[-1]],key[6]]
            self.boxes[key]=(suffix_range(a,max(self.memory,key[0])),suffix_range(b,max(self.memory,key[1])),
                             (self.power(key[6]),self.power(end+1)))
        return self.boxes[key]
    def identifier(self,key):
        la=self.side_ids[(key[0],key[2],key[4])];lb=self.side_ids[(key[1],key[3],key[5])]
        return (((la*self.S+lb)*self.B+key[6]-self.low)*self.T+self.type_ids[key[-1]])
    def coordinates(self,a,b):
        r,s,rho=parameters(a,b);z=(1+r*anchor(a))/(1+s*anchor(b));return r,s,rho*z*z
    @lru_cache(maxsize=50000)
    def child_geometry(self,parent,u,w):
        a,b=self.prototype(parent);box=self.box(parent)
        rr,ss,_=child_box(box,u,w)
        fa=derivative_fraction(a,u,box[0]);fb=derivative_fraction(b,w,box[1])
        mapped=(box[2][0]*fb[0]/fa[1],box[2][1]*fb[1]/fa[0])
        lo,hi=self.index(mapped[0]),self.index(mapped[1])
        if mapped[1]==self.power(hi):hi-=1
        if lo<self.low or hi>self.high:return None
        return a+u,b+w,rr,ss,lo,hi
    def child_keys(self,parent,u,w,typ):
        mapped=self.child_geometry(parent,u,w)
        if mapped is None:return None
        a,b,rr,ss,lo,hi=mapped
        keys=[self.key(a,b,typ,i) for i in range(lo,hi+1)]
        if any(k is None for k in keys):return None
        keys=sorted(set(keys))
        for k in keys:assert contains(self.box(k)[:2],(rr,ss))
        return keys
    def process(self,key):
        a,b=self.prototype(key);proof=AnchorUniform(a,b,key[-1],self.box(key))
        candidates=[];mapping={};n=self.meta['spine_depth']
        def spine(word):
            pre,period=extremal_tail(scan(word),len(word)%2==0)
            return (pre+period*(n+1))[:n]
        sa,sb=spine(a),spine(b)
        pl,ph=proof.numeric(((),(),key[-1]))
        for i,j,restricted in self.ps:
            u,w=self.exts[i],self.exts[j]
            if restricted and (u[:-1]!=sa[:len(u)-1] or w[:-1]!=sb[:len(w)-1]):continue
            if scan(a+u) is None or scan(b+w) is None:continue
            full=False;t2=False;l2=False;r2=False
            for typ in self.types:
                if full:break
                if t2 and typ in ('L2','R2','B2'):continue
                if (l2 or r2) and typ=='B2':continue
                keys=self.child_keys(key,u,w,typ)
                if keys is None:continue
                if any(self.identifier(k) not in self.allowed or self.states.get(k)=='rejected' for k in keys):continue
                lo,hi=proof.numeric((u,w,typ))
                if hi<pl-1e-12 or lo>ph+1e-12:continue
                candidates.append((lo,hi,u,w,typ));mapping[u,w,typ]=keys
                if typ=='F':full=True
                if typ=='T2':t2=True
                if typ=='L2':l2=True
                if typ=='R2':r2=True
        # Prefer already certified destinations among otherwise comparable
        # candidates; every edge still receives an exact covering check.
        candidates.sort(key=lambda v:(sum(self.states.get(k)!='certified_local' for k in mapping[v[2],v[3],v[4]]),
                                      len(mapping[v[2],v[3],v[4]]),len(v[2])+len(v[3])))
        menu=proof.select(candidates)
        old=self.rows.get(key)
        if old:
            for c in old['children']:self.reverse[c].discard(key)
        if menu is None:
            self.states[key]='rejected';self.rows.pop(key,None)
            for parent in sorted(self.reverse[key]):
                if self.states.get(parent)!='rejected':self.schedule(parent,urgent=True)
            return 'no_exact_closed_menu',proof.checks
        assert proof.verify(menu)
        children=set(c for v in menu for c in mapping[v])
        self.rows[key]={'menu':menu,'children':children,'counts':{'candidates':len(candidates)},'uniform_comparisons':proof.checks}
        self.states[key]='certified_local'
        for child in sorted(children):
            self.reverse[child].add(key)
            if child not in self.states:self.states[child]='pending'
            if self.states[child]=='pending':self.schedule(child)
        return 'exact_local_cover',proof.checks


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('kernel');p.add_argument('--type',default='T2')
    p.add_argument('--steps',type=int,default=3000);p.add_argument('--seconds',type=float,default=240)
    p.add_argument('--group',type=int,default=1)
    p.add_argument('--output',default='closed_kernel.json');args=p.parse_args()
    c=ClosedKernel(args.kernel,args.group);result=c.run((3,2,1,1,3),(4,3,2,2),args.type,args.steps,args.seconds)
    result['settings']['coordinate']='lower_endpoint_derivative_ratio';result['source_kernel']=args.kernel
    result['source_was_numerical_fixed_point']=c.source_fixed_point
    result['settings']['group']=args.group
    (BASE/args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'proof_complete':result['proof_complete'],'root_state':result['root_state'],
                      'rows':len(result['rows']),'reachable':len(result['reachable'])}),flush=True)
