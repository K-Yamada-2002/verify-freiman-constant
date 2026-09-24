#!/usr/bin/env python3
"""Exact two-parameter polynomial checks for a periodic upper restart strip.

x represents the outer 313121 exponent, y the upper-extreme period exponent.
Zero exponents are separate cases. Positive indices use [0,1/85]^2.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
from functools import lru_cache
import importlib.util,json,sys,argparse
from sympy.polys.rings import ring
from search_restart_covers import l,need
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'Freiman_Hall_ray_verification/verification/families/section15_late/independent_engine.py'
spec=importlib.util.spec_from_file_location('strip_field',SOURCE)
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
R,x,y=ring('x,y',f.FIELD)

def scalar(z):return R.ground_new((z if isinstance(z,f.E) else f.E(z)).v)
def mat(word):
    a,b,c,d=R.one,R.zero,R.zero,R.one
    for digit in word:a,b,c,d=b,a+int(digit)*b,d,c+int(digit)*d
    return a,b,c,d
def mm(a,b):return tuple(a[2*i]*b[j]+a[2*i+1]*b[2+j] for i in range(2) for j in range(2))
def product(*matrices):
    out=mat('')
    for m in matrices:out=mm(out,m)
    return out

def power_parameter(word,z,zero):return mat('') if zero else tuple(a-z*b for a,b in zip(mat(word),mat('')))
def matrices(nzero,mzero):
    P=power_parameter('313121',x,nzero)
    L=power_parameter('131213',y,mzero);V=power_parameter('131312',y,mzero)
    return product(mat('3211'),P,mat('33'),L),product(mat('4322'),P,V)
def det(m):return m[0]*m[3]-m[1]*m[2]
def den(m,t):return m[2]*scalar(t)+m[3]
def wd(m):return den(m,f.A)*den(m,f.B)
@lru_cache(None)
def tail(word):return f.cf(tuple(map(int,word)),f.Z)
def delta(ms,a,b):
    u,v=map(tail,a);up,vp=map(tail,b)
    return scalar(u-up)*den(ms[1],v)*den(ms[1],vp)+scalar(v-vp)*den(ms[0],u)*den(ms[0],up)
def coeff(c):return [str(v) for v in f.coords(c)]
def bernstein(pol):
    degrees=tuple(max((ij[k] for ij in pol),default=0) for k in (0,1));out=[]
    for i in range(degrees[0]+1):
        for j in range(degrees[1]+1):
            value=f.FIELD.zero
            for (a,b),c in pol.items():
                if a<=i and b<=j:
                    q=Q(comb(i,a),comb(degrees[0],a))*Q(comb(j,b),comb(degrees[1],b))*Q(1,85)**(a+b)
                    value+=c*f.FIELD.convert(q)
            out.append(value)
    return degrees,out

def assemble_chain():
    a=json.loads((HERE/'upper_m0_ray6_d3.json').read_text())
    b=json.loads((HERE/'upper_gap_bridge.json').read_text())['certificate']
    rows=[row for c in a['components'][3:] for row in c['chain']]+[row for c in b['components'] for row in c['chain']]
    K=lambda r:l.K(r['a'],r['b'],r['radicand'])
    lo=K(a['components'][3]['lower']);hi=K(a['components'][-1]['upper']);pos=lo;chain=[]
    while pos<hi:
        candidates=[r for r in rows if K(r['lower'])<=pos<K(r['upper'])]
        need(bool(candidates),'strip chain connection')
        r=max(candidates,key=lambda r:K(r['upper']));chain.append(tuple(r['suffixes']));pos=K(r['upper'])
    return chain

class Proof:
    def __init__(self,nzero,mzero,core=False):
        self.nz=nzero;self.mz=mzero;self.ms=matrices(nzero,mzero);self.records=[];self.cache={};self.normcache={}
        self.base=('3211'+('' if nzero else '313121')+'33'+('' if mzero else '131213'),
                   '4322'+('' if nzero else '313121')+('' if mzero else '131312'))
        if core:
            P=power_parameter('313121',x,nzero)
            self.ms=(product(mat('3211'),P),product(mat('4322'),P))
            self.base=('3211'+('' if nzero else '313121'),'4322'+('' if nzero else '313121'))
        need(det(self.ms[0])==det(self.ms[1]),'common positive determinant factor')
        for side,m in enumerate(self.ms):
            self.record('positive_C',m[2],True,dict(side=side));self.record('positive_D',m[3],True,dict(side=side))
        # Nonzero determinant at actual recurrence points follows from f(x)>0,
        # already proved by recurrence; positivity on the larger box is not needed.
    def record(self,name,pol,strict=True,meta=None):
        degree,co=bernstein(pol);ok=all(f.sgn(c)>0 if strict else f.sgn(c)>=0 for c in co)
        self.records.append(dict(name=name,strict=strict,meta=meta,degree=degree,
            polynomial=[dict(powers=k,coefficient=coeff(c)) for k,c in sorted(pol.items())],
            bernstein=[coeff(c) for c in co],positive=ok))
        if not ok:print('OPEN',self.nz,self.mz,name,meta,flush=True)
    def mats(self,ws):return tuple(mm(m,mat(w)) for m,w in zip(self.ms,ws))
    def normal(self,ws):
        if ws in self.normcache:return self.normcache[ws]
        pair=tuple(a+w for a,w in zip(self.base,ws));wide=l.wider(pair);m=self.mats(ws)
        self.record('full_width',wd(m[1-wide])-wd(m[wide]),wide==1,dict(words=ws,wider=wide))
        self.normcache[ws]=wide;return wide
    def endpoint(self,ws,end):
        key=ws,end
        if key in self.cache:return self.cache[key]
        wide=self.normal(ws);par=tuple(len(w)%2 for w in ws)
        if par[0]!=par[1] and ((end=='hi')==(par[wide]==0)):
            vv=list(ws);vv[wide]+='1';ans=self.endpoint(tuple(vv),end)
        else:
            e3=[(end=='lo')!=bool(p) for p in par]
            modes=[(c+w).endswith('31' if a else '3') for c,w,a in zip(self.base,ws,e3)]
            if par[0]==par[1] and not any(modes):
                suffix='3' if e3[0] else '13';m=self.mats(tuple(w+suffix for w in ws))
                pair=tuple(a+w+suffix for a,w in zip(self.base,ws))
                short=l.width(pair[wide])<=Q(7,5)*l.width(pair[1-wide])
                pol=7*wd(m[wide])-5*wd(m[1-wide])
                self.record('auxiliary_cut',pol if short else -pol,not short,dict(words=ws,end=end,wider=wide,short=short))
                if short:modes[1-wide]=True
            ans=tuple(w+(('213' if mode else '3') if a else ('1213' if mode else '13')) for w,a,mode in zip(ws,e3,modes))
        sample=l.endpoint_words(tuple(a+w for a,w in zip(self.base,ws)),end)
        need(sample==tuple(a+w for a,w in zip(self.base,ans)),'literal endpoint cross-check')
        self.cache[key]=ans;return ans
    def comparison(self,name,a,b):self.record(name,delta(self.ms,a,b),True,dict(upper=a,lower=b))
    def good(self,ws):
        pair=tuple(a+w for a,w in zip(self.base,ws))
        need(all('31313' not in w and not w.endswith(('313','3131')) for w in pair),'unmarked legal root')
        wide=self.normal(ws)
        need(len(ws[0])%2==len(ws[1])%2 or not pair[wide].endswith('31'),'first-step restart guard')
        self.comparison('nonempty',self.endpoint(ws,'hi'),self.endpoint(ws,'lo'))
        forks=[]
        for digit in ('1','2'):
            vv=list(ws);vv[wide]+=digit;vv=tuple(vv);forks.append(vv)
            self.comparison('nonempty_fork',self.endpoint(vv,'hi'),self.endpoint(vv,'lo'))
        for i,j in ((0,1),(1,0)):
            self.comparison('fork_contact',self.endpoint(forks[i],'hi'),self.endpoint(forks[j],'lo'))
    def run(self,chain):
        for w in chain:self.good(w)
        for a,b in zip(chain,chain[1:]):
            self.comparison('chain_contact',self.endpoint(a,'hi'),self.endpoint(b,'lo'))
            self.comparison('chain_reverse_contact',self.endpoint(b,'hi'),self.endpoint(a,'lo'))
        future=('131213'+chain[0][0],'131312'+chain[0][1])
        self.comparison('periodic_contact',self.endpoint(chain[-1],'hi'),self.endpoint(future,'lo'))
        return dict(n_zero=self.nz,m_zero=self.mz,chain=chain,records=self.records,
                    positive=all(r['positive'] for r in self.records))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'uniform_periodic_strip.json');args=ap.parse_args()
    cases=[]
    for nz,mz in ((True,True),(True,False),(False,True),(False,False)):
        chain=list(map(tuple,json.loads((HERE/f'period_strip_n{0 if nz else 1}_m{0 if mz else 1}.json').read_text())['chain']))
        print('chain',nz,mz,len(chain),flush=True)
        row=Proof(nz,mz).run(chain);cases.append(row)
        print('CASE',nz,mz,'positive',row['positive'],'records',len(row['records']),flush=True)
        args.output.write_text(json.dumps(dict(status='UNIFORM_STRIP_PROVED' if len(cases)==4 and all(r['positive'] for r in cases) else 'OPEN',box=['0 <= x <= 1/85','0 <= y <= 1/85'],cases=cases),indent=2)+'\n')
