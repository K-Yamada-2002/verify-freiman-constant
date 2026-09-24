#!/usr/bin/env python3
"""Independent stdlib checker: literal endpoint rules + four rational coordinates.

No search, SymPy, primary polynomial implementation, or positive flags imported.
Reconstructs every required inequality and recovers power coefficients by finite
Bernstein differences. All expected records are consumed in order.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import importlib.util,json,sys,hashlib
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'Freiman_Hall_ray_verification/verification/families/section14/exact.py'
spec=importlib.util.spec_from_file_location('rational_field',SOURCE)
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
K=f.K

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)
def clean(p):return {k:v for k,v in p.items() if v!=0}
def const(c):return clean({(0,0):K(c)})
def add(a,b):
    r=a.copy()
    for k,v in b.items():r[k]=r.get(k,K())+v
    return clean(r)
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def scale(a,c):return clean({k:v*c for k,v in a.items()})
def mul(a,b):
    r={}
    for (i,j),v in a.items():
        for (u,w),z in b.items():r[i+u,j+w]=r.get((i+u,j+w),K())+v*z
    return clean(r)
def matrix(word):return tuple(const(z) for z in f.matrix(tuple(map(int,word))))
def mm(a,b):return tuple(add(mul(a[2*i],b[j]),mul(a[2*i+1],b[2+j])) for i in range(2) for j in range(2))
def product(*args):
    r=matrix('')
    for m in args:r=mm(r,m)
    return r
def parameter(word,axis,zero):
    if zero:return matrix('')
    z={(1,0) if axis==0 else (0,1):K(1)}
    return tuple(sub(a,mul(z,b)) for a,b in zip(matrix(word),matrix('')))
def determinant(m):return sub(mul(m[0],m[3]),mul(m[1],m[2]))
def den(m,t):return add(scale(m[2],t),m[3])
def wd(m):return mul(den(m,f.LO),den(m,f.HI))
def tail(w):return f.cf(tuple(map(int,w)),f.TAILS[(1,2)])
def delta(ms,aa,bb):
    a,b=map(tail,aa);c,d=map(tail,bb)
    return add(scale(mul(den(ms[1],b),den(ms[1],d)),a-c),scale(mul(den(ms[0],a),den(ms[0],c)),b-d))
def state(word):
    need('31313' not in word,'forbidden base or extension')
    return next((s for s in ('3131','313','31','3') if word.endswith(s)),'')
def repeated(prefix,period,zero):
    if zero:state(prefix);return prefix
    first=prefix+period;second=first+period
    need(state(first)==state(second),'finite automaton return for arbitrary powers')
    return first

def parse_pol(rows):
    r={}
    for row in rows:
        key=tuple(row['powers']);need(len(key)==2 and all(isinstance(i,int) and i>=0 for i in key),'monomial index')
        need(key not in r,'duplicate monomial');r[key]=K(*map(F,row['coefficient']))
    return clean(r)

class Checker:
    def __init__(self,row,core=False):
        self.row=row;self.i=0;self.core=core;self.cache={};self.normcache={};self.coefficients=0
        nz=row['n_zero'];mz=row.get('m_zero',True)
        p=parameter('313121',0,nz)
        L=product(matrix('3211'),p);V=product(matrix('4322'),p)
        base=(repeated('3211','313121',nz),repeated('4322','313121',nz))
        if not core:
            L=product(L,matrix('33'),parameter('131213',1,mz))
            V=product(V,parameter('131312',1,mz))
            base=(repeated(base[0]+'33','131213',mz),repeated(base[1],'131312',mz))
        self.ms=(L,V);self.base=base
        need(all(len(w)%2==0 for w in base),'even base signs')
        expected=const(1)
        for axis,zero in ((0,nz),(1,mz or core)):
            if not zero:expected=mul(expected,{(0,0):K(1),(1,0) if axis==0 else (0,1):K(-86),(2,0) if axis==0 else (0,2):K(1)})
        need(determinant(L)==expected and determinant(V)==expected,'common recurrence determinant identity')
        for side,m in enumerate(self.ms):
            self.record('positive_C',m[2],True,dict(side=side));self.record('positive_D',m[3],True,dict(side=side))
    def peek(self):
        need(self.i<len(self.row['records']),'missing obligation');return self.row['records'][self.i]
    def record(self,name,pol,strict=True,meta=None):
        row=self.peek();self.i+=1
        need(row['name']==name and row['strict']==strict,'record name/strictness')
        need(json.dumps(row['meta'],sort_keys=True)==json.dumps(meta,sort_keys=True),'record metadata')
        need(parse_pol(row['polynomial'])==pol,'independently reconstructed polynomial '+name)
        degree=tuple(max((key[k] for key in pol),default=0) for k in (0,1))
        need(tuple(row['degree'])==degree,'exact polynomial degree')
        co=[K(*map(F,c)) for c in row['bernstein']];dx,dy=degree
        need(len(co)==(dx+1)*(dy+1),'complete coefficient table')
        need(all(c.sign()>0 if strict else c.sign()>=0 for c in co),'exact sign '+name)
        reconstructed={}
        for u in range(dx+1):
            for v in range(dy+1):
                z=K()
                for i in range(u+1):
                    for j in range(v+1):z+=co[i*(dy+1)+j]*((-1)**(u+v-i-j)*comb(u,i)*comb(v,j))
                reconstructed[u,v]=z*(85**(u+v)*comb(dx,u)*comb(dy,v))
        need(clean(reconstructed)==pol,'inverse Bernstein identity')
        self.coefficients+=len(co)
    def mats(self,ws):return tuple(mm(m,matrix(w)) for m,w in zip(self.ms,ws))
    def normal(self,ws):
        if ws in self.normcache:return self.normcache[ws]
        wide=self.peek()['meta']['wider'];need(wide in (0,1),'wider choice')
        m=self.mats(ws)
        self.record('full_width',sub(wd(m[1-wide]),wd(m[wide])),wide==1,dict(words=ws,wider=wide))
        self.normcache[ws]=wide;return wide
    def endpoint(self,ws,end):
        key=ws,end
        if key in self.cache:return self.cache[key]
        wide=self.normal(ws);par=tuple(len(w)%2 for w in ws)
        if par[0]!=par[1] and ((end=='hi')==(par[wide]==0)):
            vv=list(ws);vv[wide]+='1';ans=self.endpoint(tuple(vv),end)
        else:
            three=[(end=='lo')!=bool(p) for p in par]
            modes=[(c+w).endswith('31' if a else '3') for c,w,a in zip(self.base,ws,three)]
            if par[0]==par[1] and not any(modes):
                short=self.peek()['meta']['short'];need(type(short)is bool,'endpoint shortening choice')
                suffix='3' if three[0] else '13';m=self.mats(tuple(w+suffix for w in ws))
                pol=sub(scale(wd(m[wide]),7),scale(wd(m[1-wide]),5))
                self.record('auxiliary_cut',pol if short else neg(pol),not short,dict(words=ws,end=end,wider=wide,short=short))
                if short:modes[1-wide]=True
            ans=tuple(w+(('213' if short else '3') if a else ('1213' if short else '13')) for w,a,short in zip(ws,three,modes))
        for base,w in zip(self.base,ans):state(base+w+'1212')
        self.cache[key]=ans;return ans
    def comparison(self,name,a,b):self.record(name,delta(self.ms,a,b),True,dict(upper=a,lower=b))
    def good(self,ws):
        need(all(set(w)<=set('123') for w in ws),'added alphabet')
        for base,w in zip(self.base,ws):need(state(base+w) not in ('313','3131'),'unmarked restart')
        wide=self.normal(ws)
        need(len(ws[0])%2==len(ws[1])%2 or not (self.base[wide]+ws[wide]).endswith('31'),'first-step guard')
        self.comparison('nonempty',self.endpoint(ws,'hi'),self.endpoint(ws,'lo'))
        forks=[]
        for digit in ('1','2'):
            vv=list(ws);vv[wide]+=digit;vv=tuple(vv);forks.append(vv)
            self.comparison('nonempty_fork',self.endpoint(vv,'hi'),self.endpoint(vv,'lo'))
        for i,j in ((0,1),(1,0)):self.comparison('fork_contact',self.endpoint(forks[i],'hi'),self.endpoint(forks[j],'lo'))
    def run(self):
        chain=list(map(tuple,self.row['chain']))
        if self.core:
            need(chain==[('3',''),('33','11')],'specified root connection')
            for w in chain:self.good(w)
            self.comparison('lower_initial_to_root',('31331213','331213'),self.endpoint(chain[0],'lo'))
            self.comparison('root_to_upper_strip',self.endpoint(chain[0],'hi'),self.endpoint(chain[1],'lo'))
            self.comparison('root_to_upper_strip_reverse',self.endpoint(chain[1],'hi'),self.endpoint(chain[0],'lo'))
        else:
            need(chain and chain[0]==('','11') and chain[-1]==('131213','13131211'),'same restart at successive periods')
            for w in chain:self.good(w)
            for a,b in zip(chain,chain[1:]):
                self.comparison('chain_contact',self.endpoint(a,'hi'),self.endpoint(b,'lo'))
                self.comparison('chain_reverse_contact',self.endpoint(b,'hi'),self.endpoint(a,'lo'))
            future=('131213'+chain[0][0],'131312'+chain[0][1])
            self.comparison('periodic_contact',self.endpoint(chain[-1],'hi'),self.endpoint(future,'lo'))
        need(self.i==len(self.row['records']),'no extra unused obligations')
        return dict(records=self.i,coefficients=self.coefficients)

def verify_file(path,core):
    data=json.loads(path.read_text());rows=data['cases']
    need(data['box']==(['0 <= x <= 1/85','y unused'] if core else ['0 <= x <= 1/85','0 <= y <= 1/85']),'declared parameter domain')
    expected=[(True,True),(True,False),(False,True),(False,False)] if not core else [(True,True),(False,True)]
    need([(r['n_zero'],r.get('m_zero',True)) for r in rows]==expected,'exhaustive exponent cases')
    results=[]
    for row in rows:
        result=Checker(row,core).run();results.append(result)
        print('PASS',path.name,row['n_zero'],row.get('m_zero',True),result,flush=True)
    return dict(path=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),cases=results)

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--strip',type=Path,default=HERE/'uniform_periodic_strip.json')
    ap.add_argument('--connection',type=Path,default=HERE/'uniform_root_connection.json');ap.add_argument('--output',type=Path,default=HERE/'independent_uniform_replay.json');a=ap.parse_args()
    results=[verify_file(a.strip,False),verify_file(a.connection,True)]
    a.output.write_text(json.dumps(dict(status='PASS_INDEPENDENT_UNIFORM_ARITHMETIC',results=results,
        scope='All-index strip and root-connection arithmetic. Restart and lower-subsystem lemmas remain written proof dependencies.'),indent=2)+'\n')
