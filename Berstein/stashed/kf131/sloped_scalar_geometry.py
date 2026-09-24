"""Exact affine bands G - k*h in the anchored scalar coordinate.

A case may join ratio boxes only when they use the same rational slope.
The distinct schema prevents old constant-interval repair tools from silently
interpreting these bands as constant scalar intervals.
"""
from exact import F,extreme_tail,matrix,state_of,transform
from anchored_geometry import ALPHA,B,delta_range,parameters
from scalar_geometry import quadratic_range
from verify_scalar_graph import ScalarVerifier
from verify_type_graph import require


def band_endpoint(u,v,swap,endpoint,child_slope,parent_slope,rbox,sbox,hbox,parity):
    require(type(swap) is bool and parity in (-1,1),'invalid band exchange or parity')
    eu,ev=(-1)**len(u),(-1)**len(v)
    left_coefficient=parity*ev*child_slope if swap else eu*endpoint
    right_coefficient=ev*endpoint if swap else parity*eu*child_slope
    left=quadratic_range(u,left_coefficient,tuple(rbox))
    right=quadratic_range(v,right_coefficient,tuple(sbox))
    if parity<0:
        right=-right[1],-right[0]
    right=right[0]-parent_slope,right[1]-parent_slope
    require(0<hbox[0]<=hbox[1],'invalid band ratio')
    products=[h*t for h in hbox for t in right]
    return left[0]+min(products),left[1]+max(products)


def band_core(u,v,swap,interval,child_slope,parent_slope,rbox,sbox,hbox,parity):
    a,b=interval
    require(a<b,'empty band interval')
    sign=parity*(-1)**len(v) if swap else (-1)**len(u)
    if sign<0:
        a,b=b,a
    lo=band_endpoint(u,v,swap,a,child_slope,parent_slope,rbox,sbox,hbox,parity)[1]
    hi=band_endpoint(u,v,swap,b,child_slope,parent_slope,rbox,sbox,hbox,parity)[0]
    return lo,hi


class SlopedScalarVerifier(ScalarVerifier):
    def __init__(self,data):
        require(data.get('schema')=='kf131-sloped-atlas-v1','wrong affine-band schema')
        super().__init__(dict(data,schema='kf131-scalar-atlas-v1'))
        self.data=data
        self.slopes=[F(n['scalar_slope']) for n in self.nodes]

    def initial_hull(self,index):
        n=self.nodes[index]; p=n['parity']; sl,sr=map(state_of,n['states'])
        rb,sb,hb=self.box(index); k=self.slopes[index]
        def bounds(high):
            x=extreme_tail(sl,high)[0]
            y=extreme_tail(sr,high if p>0 else not high)[0]
            left=delta_range(x,ALPHA,rb); right=delta_range(y,ALPHA,sb)
            if p<0:
                right=-right[1],-right[0]
            products=[h*(t-k) for h in hb for t in right]
            return left[0]+min(products),left[1]+max(products)
        return bounds(False)[1],bounds(True)[0]

    def transport(self,index,u,v,swap,interval,destinations):
        slopes={self.slopes[j] for j in destinations}
        require(len(slopes)==1,'mixed child slopes need a slanted product-cover proof')
        return band_core(u,v,swap,interval,next(iter(slopes)),self.slopes[index],
                         *self.box(index),self.nodes[index]['parity'])

    def seed(self):
        # Parent verification checks legality, parameter inclusion and parity.
        super().seed()
        root=self.data['roots'][0]; u,v=self.data['root_prefixes']
        _,_,h,_=parameters(u,v)
        _,_,c,d=matrix(u)
        scale=(-1)**len(u)/(c*ALPHA+d)**2
        center=transform(u,ALPHA)+transform(v,ALPHA)
        values=sorted(center+scale*(t+self.slopes[root]*h)
                      for t in self.interval(self.nodes[root]['interval']))
        require(values[0]<values[1],'degenerate band seed')
        return [x.record() for x in values]
