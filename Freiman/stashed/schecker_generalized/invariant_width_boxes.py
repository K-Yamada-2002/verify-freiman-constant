#!/usr/bin/env python3
"""Box-invariant discovery normalized by actual restricted cylinder widths.

The variable w is the right/left width ratio, not denominator ratio q.
Floating discovery only; nonempty output is not a proof until replayed.
"""
import argparse,json,math
from functools import lru_cache
from pathlib import Path
import invariant_boxes as ib
from explore import extreme_tail,state_of


@lru_cache(None)
def reference(state):return tuple(extreme_tail(state_of(state),high)[0] for high in (False,True))


@lru_cache(None)
def delta_range(x,y,state,rb):
    lo,hi=reference(state)
    if x==y:return (0.0,0.0)
    if x==hi and y==lo:return (1.0,1.0)
    if x==lo and y==hi:return (-1.0,-1.0)
    x,y,l,h=map(lambda z:float(z.decimal()),(x,y,lo,hi))
    a,b=l+h,l*h;c,d=x+y,x*y
    aa,bb,cc=b*c-a*d,2*(b-d),a-c
    points=list(map(float,rb))
    if abs(aa)<1e-16:
        if abs(bb)>1e-16:
            root=-cc/bb
            if points[0]<root<points[1]:points.append(root)
    else:
        disc=bb*bb-4*aa*cc
        if disc>=0:
            for root in ((-bb-math.sqrt(disc))/(2*aa),(-bb+math.sqrt(disc))/(2*aa)):
                if points[0]<root<points[1]:points.append(root)
    values=[(x-y)/(h-l)*(1+a*r+b*r*r)/(1+c*r+d*r*r) for r in points]
    return min(values)-2e-14,max(values)+2e-14


class WidthBoxSearch(ib.BoxSearch):
    def ge(self,a,b,rb,sb,wb,p,si,ti):
        if a==b:return True
        dl=delta_range(a[0],b[0],ib.STATES[si],rb)[0]
        dr=delta_range(a[1],b[1],ib.STATES[ti],sb)
        lower=dr[0] if p>0 else -dr[1]
        w=float(wb[0] if lower>=0 else wb[1])
        return dl+w*lower>1e-11

    def point(self,pair,rb,sb,wb,p,si,ti):
        r,s,w=map(lambda z:float(sum(z)/2),(rb,sb,wb))
        def position(x,state,z):
            l,h=reference(state);x,l,h=map(lambda a:float(a.decimal()),(x,l,h))
            return (x-l)/(h-l)*(1+z*h)/(1+z*x)
        return position(pair[0],ib.STATES[si],r)+p*w*position(pair[1],ib.STATES[ti],s)

    def image_range(self,s,t,p,u,v,rb,sb,wb):
        ep=ib.endpoints(s,t,p,0,u,v)
        x,y=sorted((ep[0][0],ep[1][0]));z,w=sorted((ep[0][1],ep[1][1]))
        dl=delta_range(y,x,s,rb);dr=delta_range(w,z,t,sb)
        return float(wb[0])*dr[0]/dl[1],float(wb[1])*dr[1]/dl[0]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--states',type=int,choices=(6,13),default=6)
    ap.add_argument('--bins',type=int,default=17)
    ap.add_argument('--max-step',type=int,default=2)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if args.states==13:ib.STATES,ib.RANGES=ib.STATES13,ib.RANGES13
    search=WidthBoxSearch(args.bins,args.max_step)
    print('prepared',len(search.nodes),'nodes',sum(map(len,search.offers)),'offers',flush=True)
    alive,plans,history=search.run()
    data=search.save(alive,plans,history)
    data['ratio_parameter']='actual restricted right/left cylinder width ratio'
    print('survivors',len(alive),'closed',data['closed'],flush=True)
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
