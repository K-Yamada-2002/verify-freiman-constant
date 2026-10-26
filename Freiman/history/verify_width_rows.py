"""Independent polynomial proof of width-coordinate local covering rows.

Clear positive denominators and certify the resulting polynomial by tensor
Bernstein coefficients. This does not call WidthUniform.ge or its interval
range evaluator. The polynomial is quadratic in r,s and linear in R.
It verifies local coverage only, not the table's successor closure.
"""
import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from layout import DATA
from typed_intervals import endpoints
from typed_boxes import Uniform
from obstruction_probe import scan
from verify_typed import sign


@lru_cache(maxsize=20000)
def bernstein(u,v,bounds):
    lo,hi=bounds
    value=lambda r:(1+r*u)*(1+r*v)
    return value(lo),value(lo)+(hi-lo)*(u+v+2*lo*u*v)/2,value(hi)


class BernsteinUniform(Uniform):
    def ge(self,x,y):
        key=x,y
        if key not in self.cache:self.cache[key]=self.prove(x,y,self.box,0)
        return self.cache[key]
    def prove(self,x,y,box,depth):
        ma,Ma=endpoints(scan(self.a),'base');mb,Mb=endpoints(scan(self.b),'base')
        aa=bernstein(ma,Ma,box[0]);bb=bernstein(x[1],y[1],box[1])
        cc=bernstein(x[0],y[0],box[0]);dd=bernstein(mb,Mb,box[1])
        left=(-1)**len(self.a)*(x[0]-y[0])*(Mb-mb)
        right=(-1)**len(self.b)*(x[1]-y[1])*(Ma-ma)
        signs=[[[sign(left*aa[i]*bb[j]+R*right*cc[i]*dd[j])
                 for j in range(3)] for i in range(3)] for R in box[2]]
        if all(v>=0 for layer in signs for row in layer for v in row):return True
        # Negative corner is an actual counterexample to this witness pair.
        if any(layer[i][j]<0 for layer in signs for i in (0,2) for j in (0,2)):return False
        if depth>=8:return False
        axis=depth%2;lo,hi=box[axis];mid=(lo+hi)/2
        for bounds in ((lo,mid),(mid,hi)):
            child=list(box);child[axis]=bounds
            if not self.prove(x,y,tuple(child),depth+1):return False
        return True


def main():
    p=argparse.ArgumentParser();p.add_argument('input',nargs='?',default='width_oriented_cached.json')
    p.add_argument('--output',default='width_rows_verification.json');args=p.parse_args()
    base=DATA;data=json.loads((base/args.input).read_text())
    assert data['settings']['coordinate']=='persistent_width_ratio'
    n=0;failures=[]
    for row in data['rows']:
        a,b=map(tuple,row['prototype']);box=tuple(tuple(map(Q,p)) for p in row['box'])
        menu=[(tuple(u),tuple(w),t) for u,w,t in row['menu']]
        assert all(len(u)+len(w)>0 and scan(a+u) is not None and scan(b+w) is not None for u,w,t in menu)
        if BernsteinUniform(a,b,row['key'][-1],box).verify(menu):n+=1
        else:failures.append(row['id'])
        if (n+len(failures))%100==0:print(json.dumps({'verified':n,'unverified':len(failures)}),flush=True)
    from width_catalog import WidthCatalog
    a,b=(3,2,1,1,3),(4,3,2,2)
    point=tuple((x,x) for x in WidthCatalog().coordinates(a,b))
    control=BernsteinUniform(a,b,'F',point)
    assert control.verify([((1,),(),'F'),((),(1,),'F')])
    assert not control.verify([((1,),(),'F')])
    assert not control.verify([((),(1,),'F')])
    result={'input':args.input,'passed':not failures,'independent_polynomial_local_rows':n,
            'unverified_row_ids':failures,'corruption_controls':2,
            'closure_checked':False,'freiman_ray_proved':False}
    (base/args.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
    if failures:raise SystemExit(1)


if __name__=='__main__':main()
