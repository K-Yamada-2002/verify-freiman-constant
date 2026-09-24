#!/usr/bin/env python3
"""Find gaps in the three actual child families; certify witnesses exactly."""
from functools import lru_cache
from fractions import Fraction as F
import argparse,json
from pathlib import Path
from explore import *
from search_types import Search,tail


def numeric_sides(u,v,depth):
    r,s,q,el,er,_,_=Search().parameters(u,v)
    answer=[]
    for word,coef,ratio in ((u,el,r),(v,er*q,s)):
        parts=[]
        for full in extensions(word,depth):
            suffix=full[len(word):];a,b,c,d=matrix(suffix)
            vals=[]
            for high in (False,True):
                x=tail(state_of(full),high);x=(a*x+b)/(c*x+d)
                vals.append(coef*x/(1+ratio*x))
            parts.append((min(vals),max(vals),full))
        answer.append(sorted(parts))
    return answer


def discover(u,v,depth,kind):
    left,right=numeric_sides(u,v,depth)
    s=Search();target=s.parameters(u,v)[-2]
    if kind=='J':
        r,ss,q,el,er,_,_=s.parameters(u,v)
        xi=float(extreme_tail('',False)[0].decimal())
        x=1/(2+xi);y=1/(1+xi)
        target=(el*x/(1+r*x)+er*q*y/(1+ss*y),target[1])
    intervals=sorted((a+c,b+d,i,j) for i,(a,b,_) in enumerate(left)
                     for j,(c,d,_) in enumerate(right))
    gaps_found=[];current=intervals[0]
    for row in intervals[1:]:
        if row[0]>current[1]+1e-12:
            lo,hi=max(current[1],target[0]),min(row[0],target[1])
            if lo<hi:
                gaps_found.append((current[2:],row[2:]))
        if row[1]>current[1]:current=row
    return left,right,gaps_found


def certify(left,right,left_pair,right_pair,target):
    i,j=left_pair;k,l=right_pair
    low=hull(left[i][2],right[j][2])[1]
    high=hull(left[k][2],right[l][2])[0]
    low,high=max(low,target[0]),min(high,target[1])
    if not low<high:return None
    a=sorted(cylinder(w) for _,_,w in left)
    b=sorted(cylinder(w) for _,_,w in right)
    i=0;j=len(b)-1;steps=0
    while i<len(a) and j>=0:
        steps+=1
        if a[i][1]+b[j][1]<=low:i+=1
        elif a[i][0]+b[j][0]>=high:j-=1
        else:return None
    return {'interval':interval_record((low,high)),'exact_two_pointer_steps':steps}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=6)
    ap.add_argument('--n-max',type=int,default=1)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();rows=[];xi=extreme_tail('',False)[0]
    for n in range(args.n_max+1):
        u,v='3211'+'313121'*n+'3','4322'+'313121'*n
        for kind,a,b in [('H1',u+'1',v),('H2',u+'2',v),('J',u,v+'1')]:
            target=hull(a,b)
            if kind=='J':target=(transform(a+'2',xi)+transform(b+'1',xi),target[1])
            left,right,found=discover(a,b,args.depth,kind)
            certs=[certify(left,right,x,y,target) for x,y in found[:3]]
            certs=[x for x in certs if x is not None]
            row={'n':n,'kind':kind,'left':a,'right':b,'depth':args.depth,
                 'numeric_gap_count':len(found),'certified_gaps':certs}
            rows.append(row);print(n,kind,'numeric gaps',len(found),'certified',len(certs),flush=True)
    if args.output:args.output.write_text(json.dumps(rows,indent=2)+'\n')


if __name__=='__main__':main()
