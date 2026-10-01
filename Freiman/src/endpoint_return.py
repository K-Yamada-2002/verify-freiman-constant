"""Try a periodic endpoint-return chart, with all other children in a kernel.

The exceptional state retains the exact lower-endpoint derivative ratio. A
six-digit return preserves this ratio identically and contracts r,s. This
avoids repeatedly rounding a neutral coordinate to a fresh wide grid cell.
"""
import argparse,json,math,heapq,time
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q
from itertools import product
from exact_cf import parameters,matrix
from typed_intervals import E,cf
from typed_boxes import side_pairs
from anchor_boxes import anchor,derivative_fraction,delta_range
from width_catalog import normalized_difference_range
from box_certificates import child_box,suffix_range,contains
from obstruction_probe import scan,extremal_tail

BASE=DATA
U=(1,3,1,2,1,3);V=(3,1,3,1,2,1)
A=(3,2,1,1,3);B=(4,3,2,2)


def extrema(vals):return min(vals),max(vals)
def shape_width(word,bounds):
    x0=anchor(word);x1=side_pairs(scan(word),len(word)%2,(),'base')[1]
    vals=delta_range(x0,x1,x0,bounds)
    return (-vals[1],-vals[0]) if len(word)%2 else vals
def eta(word,u,bounds):
    result=[]
    for x in side_pairs(scan(word),len(word)%2,u,'base'):
        v=normalized_difference_range(scan(word),x,anchor(word),bounds)
        if len(word)%2:v=(-v[1],-v[0])
        result.append((max(E.cast(0),v[0]),min(E.cast(1),v[1])))
    return result
def mix(a,b,t):return tuple((1-t)*a[i]+t*b[i] for i in (0,1))
def normalized_sum(a,b,R):
    return (min((a[0]+r*b[0])/(1+r) for r in R),
            max((a[1]+r*b[1])/(1+r) for r in R))


class ReturnSearch:
    def __init__(self,name):
        self.meta=json.loads((BASE/(name+'.meta.json')).read_text());m=self.meta
        assert m['coordinate']=='lower_endpoint_derivative_ratio'
        self.ids={(q,p,tuple(s)):i for i,(q,p,s) in enumerate(m['side_keys'])}
        self.sides=len(self.ids);self.bins=m['high']-m['low']+1;self.base=Q(m['base']);self.low=m['low'];self.high=m['high']
        self.memory=m['memory'];self.types=m['types'];self.T=len(self.types)
        result=json.loads((BASE/(name+'.json')).read_text())
        replay=BASE/(name+'_replay.json')
        if replay.exists():
            checked=json.loads(replay.read_text())
            if checked.get('verification_only') and checked.get('closed_family_found'):
                assert (BASE/(name+'.json.alive.bin')).read_bytes()==(BASE/(name+'_replay.json.alive.bin')).read_bytes()
                result=checked
        self.certified=result.get('closed_family_found',False)
        if 'alive' in result:self.alive=set(result['alive'])
        else:
            bits=(BASE/(name+'.json.alive.bin')).read_bytes();self.alive={i for i,b in enumerate(bits) if b}
        self.bands=[]
        for t,kind in enumerate(self.types):
            if kind=='F':self.bands.append((t,Q(0),Q(1)))
            elif kind.startswith('band_'):
                _,a,b=kind.split('_');self.bands.append((t,Q(a),1-Q(b)))
    def index(self,S):
        lo,hi=self.low-1,self.high+2
        while lo+1<hi:
            mid=(lo+hi)//2
            if self.base**mid<=S:lo=mid
            else:hi=mid
        return lo
    def side(self,word,u,bounds):
        if scan(word+u) is None:return None
        key=(len(scan(word+u)),len(word+u)%2,(word+u)[-self.memory:])
        i=self.ids[key];newrb=child_box((bounds,(Q(0),Q(0)),(Q(1),Q(1))),u,())[0]
        proto=tuple(self.meta['prototypes'][i]);length=max(self.memory,key[0])
        if self.meta.get('prehistory_interval',['0','1'])==['0','1']:
            destination=suffix_range(proto,length)
        else:
            aa,bb,cc,dd=matrix(tuple(reversed(proto[-length:])))
            destination=tuple(sorted((aa*t+bb)/(cc*t+dd) for t in map(Q,self.meta['prehistory_interval'])))
        assert contains((destination,),(newrb,))
        return {'id':i,'r':newrb,'eta':eta(word,u,bounds),'growth':derivative_fraction(word,u,bounds)}
    def cover(self,a,b,box,delta,depth):
        r,s,S=box;wa=shape_width(a,r);wb=shape_width(b,s)
        R=(S[0]*wb[0]/wa[1],S[1]*wb[1]/wa[0])
        def words(word):
            pre,period=extremal_tail(scan(word),len(word)%2==0);sp=(pre+period*(depth+1))[:depth]
            out={w for n in range(4) for w in product((1,2,3),repeat=n)}
            out.update(sp[:n]+(d,) for n in range(depth) for d in (1,2,3))
            return sorted(out,key=lambda u:(len(u),u))
        aa={u:self.side(a,u,r) for u in words(a)};bb={w:self.side(b,w,s) for w in words(b)}
        aa={u:v for u,v in aa.items() if v is not None};bb={w:v for w,v in bb.items() if v is not None}
        loopa=self.side(a,U,r);loopb=self.side(b,V,s)
        assert cf(U,anchor(a+U))==anchor(a) and cf(V,anchor(b+V))==anchor(b)
        assert loopa['growth'][0]==loopa['growth'][1]==loopb['growth'][0]==loopb['growth'][1]
        assert contains(STABLE[:2],(loopa['r'],loopb['r']))
        loop_hi=normalized_sum(mix(*loopa['eta'],delta),mix(*loopb['eta'],delta),R)[0]
        intervals=[(E.cast(0),loop_hi,{'u':U,'w':V,'destination':'stable_return','band':[str(0),str(delta)]})]
        tested=0
        for u,x in aa.items():
            for w,y in bb.items():
                if not u and not w:continue
                if normalized_sum(x['eta'][0],y['eta'][0],R)[0]>delta:continue
                mapped=(S[0]*y['growth'][0]/x['growth'][1],S[1]*y['growth'][1]/x['growth'][0])
                if mapped[0]<self.base**self.low or mapped[1]>self.base**(self.high+1):continue
                lo,hi=self.index(mapped[0]),self.index(mapped[1])
                if mapped[1]==self.base**hi:hi-=1
                # Point intervals on a grid boundary still belong to a closed bin.
                hi=max(lo,hi)
                geom=x['id']*self.sides+y['id'];available=[]
                for typ,l,h in self.bands:
                    if all(((geom*self.bins+i-self.low)*self.T+typ) in self.alive for i in range(lo,hi+1)):
                        available.append((l,h,typ))
                joined=[]
                for l,h,t in sorted(available):
                    if joined and l<=joined[-1][1]:
                        joined[-1][1]=max(joined[-1][1],h);joined[-1][2].append(t)
                    else:joined.append([l,h,[t]])
                for l,h,types in joined:
                    il=normalized_sum(mix(*x['eta'],l),mix(*y['eta'],l),R)[1]
                    ih=normalized_sum(mix(*x['eta'],h),mix(*y['eta'],h),R)[0]
                    if il<=ih and il<=delta and ih>=0:
                        intervals.append((il,ih,{'u':u,'w':w,'destination':'kernel','band':[str(l),str(h)],
                                               'types':types,'geometry':geom,'bins':[lo,hi]}))
                tested+=1
        current=E.cast(0);chosen=[]
        while current<delta:
            choices=[iv for iv in intervals if iv[0]<=current<iv[1]]
            if not choices:break
            best=max(choices,key=lambda v:v[1]);chosen.append(best);current=best[1]
        return {'covered':current>=delta,'covered_from_zero':current.data(),'covered_decimal':float(current),
                'delta':str(delta),'tested_rectangles':tested,'menu':[v[2] for v in chosen],
                'intervals':[[v[0].data(),v[1].data()] for v in chosen]}

    def adaptive_cover(self,a,b,box,delta,max_nodes=5000,max_length=32):
        r,s,S=box;wa=shape_width(a,r);wb=shape_width(b,s)
        R=(S[0]*wb[0]/wa[1],S[1]*wb[1]/wa[0])
        acache={};bcache={}
        def get(word,u,bounds,cache):
            if u not in cache:cache[u]=self.side(word,u,bounds)
            return cache[u]
        x=get(a,U,r,acache);y=get(b,V,s,bcache)
        assert cf(U,anchor(a+U))==anchor(a) and cf(V,anchor(b+V))==anchor(b)
        assert x['growth'][0]==x['growth'][1]==y['growth'][0]==y['growth'][1]
        assert contains(STABLE[:2],(x['r'],y['r']))
        upper=normalized_sum(mix(*x['eta'],delta),mix(*y['eta'],delta),R)[0]
        intervals=[(E.cast(0),upper,{'u':U,'w':V,'destination':'stable_return','band':['0',str(delta)]})]
        covered=[(E.cast(0),upper)];queue=[(0,0,(),())];seen={((),())};serial=1;processed=0;start=time.monotonic()
        blocked=[]
        def merge():
            result=[]
            for lo,hi,*_ in sorted(intervals,key=lambda v:v[0]):
                if result and lo<=result[-1][1]:result[-1]=(result[-1][0],max(hi,result[-1][1]))
                else:result.append((lo,hi))
            return result
        while queue and processed<max_nodes:
            length,_,u,w=heapq.heappop(queue);processed+=1
            x=get(a,u,r,acache);y=get(b,w,s,bcache)
            if x is None or y is None:continue
            ol=normalized_sum(x['eta'][0],y['eta'][0],R)[0]
            oh=normalized_sum(x['eta'][1],y['eta'][1],R)[1]
            if ol>delta or oh<0:continue
            if any(lo<=max(ol,E.cast(0)) and min(oh,E.cast(delta))<=hi for lo,hi in covered):continue
            mapped=(S[0]*y['growth'][0]/x['growth'][1],S[1]*y['growth'][1]/x['growth'][0])
            if self.base**self.low<=mapped[0] and mapped[1]<=self.base**(self.high+1):
                lo,hi=self.index(mapped[0]),self.index(mapped[1])
                if mapped[1]==self.base**hi:hi-=1
                hi=max(lo,hi);geom=x['id']*self.sides+y['id'];available=[]
                for typ,l,h in self.bands:
                    if all(((geom*self.bins+i-self.low)*self.T+typ) in self.alive for i in range(lo,hi+1)):
                        available.append((l,h,typ))
                joined=[]
                for l,h,t in sorted(available):
                    if joined and l<=joined[-1][1]:joined[-1][1]=max(joined[-1][1],h);joined[-1][2].append(t)
                    else:joined.append([l,h,[t]])
                for l,h,types in joined:
                    il=normalized_sum(mix(*x['eta'],l),mix(*y['eta'],l),R)[1]
                    ih=normalized_sum(mix(*x['eta'],h),mix(*y['eta'],h),R)[0]
                    if il<=ih and il<=delta and ih>=0:
                        intervals.append((il,ih,{'u':u,'w':w,'destination':'kernel','band':[str(l),str(h)],
                                                'types':types,'geometry':geom,'bins':[lo,hi]}))
                covered=merge()
                if any(lo<=0 and hi>=delta for lo,hi in covered):break
            if length>=max_length:
                blocked.append({'u':u,'w':w,'outer':[ol.data(),oh.data()]})
                continue
            sides=('right',) if mapped[0]>self.base**(self.high+1) else (('left',) if mapped[1]<self.base**self.low else ('left','right'))
            for side in sides:
                for d in (1,2,3):
                    uu,ww=(u+(d,),w) if side=='left' else (u,w+(d,))
                    if (uu,ww) not in seen:
                        seen.add((uu,ww));heapq.heappush(queue,(length+1,serial,uu,ww));serial+=1
            if processed%250==0:
                print(json.dumps({'processed':processed,'queue':len(queue),'covered_from_zero':float(covered[0][1]),'seconds':time.monotonic()-start}),flush=True)
        current=E.cast(0);chosen=[]
        while current<delta:
            choices=[iv for iv in intervals if iv[0]<=current<iv[1]]
            if not choices:break
            best=max(choices,key=lambda v:v[1]);chosen.append(best);current=best[1]
        uncovered=[];end=E.cast(0)
        for lo,hi in covered:
            if hi<0 or lo>delta:continue
            if end<lo:uncovered.append((end,min(lo,E.cast(delta))))
            end=max(end,hi)
        if end<delta:uncovered.append((end,E.cast(delta)))
        return {'covered':current>=delta,'covered_from_zero':current.data(),'covered_decimal':float(current),
                'delta':str(delta),'processed':processed,'pending':len(queue),'seconds':time.monotonic()-start,
                'menu':[v[2] for v in chosen],'intervals':[[v[0].data(),v[1].data()] for v in chosen],
                'uncovered_decimal':[[float(lo),float(hi)] for lo,hi in uncovered],
                'uncovered_exact':[[lo.data(),hi.data()] for lo,hi in uncovered],
                'length_limit_frontier':blocked}


r0,s0,rho0=parameters(A,B);z0=(1+r0*anchor(A))/(1+s0*anchor(B));S0=rho0*z0*z0
STABLE=((Q(267649,10**6),Q(267651,10**6)),(Q(736182,10**6),Q(736231,10**6)),(S0,S0))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('kernel');p.add_argument('--depth',type=int,default=6)
    p.add_argument('--delta',default='1/8');p.add_argument('--output',default='endpoint_return.json');args=p.parse_args()
    search=ReturnSearch(args.kernel);delta=Q(args.delta)
    stable=search.cover(A+U,B+V,STABLE,delta,args.depth);print(json.dumps({'stable':stable}),flush=True)
    root=search.cover(A,B,((r0,r0),(s0,s0),(S0,S0)),delta,args.depth);print(json.dumps({'root':root}),flush=True)
    result={'kernel':args.kernel,'kernel_is_certified':search.certified,'proof_complete':search.certified and stable['covered'] and root['covered'],
            'scope':'Initial endpoint band only, not the full Freiman ray.','ratio':S0.data(),'stable':stable,'root':root}
    (BASE/args.output).write_text(json.dumps(result,indent=2)+'\n')
