#!/usr/bin/env python3
"""Exact replay of finite-horizon endpoint-type covers found by search_types.

Leaves are explicitly unproved full hulls. The certificate proves finite
refinement coverage, not filling or an infinite invariant.
"""
from fractions import Fraction as F
from collections import Counter
import argparse
import json
from pathlib import Path
from explore import Q, matrix, state_of, extreme_tail, transform, hull, restricted_ratio, merge
from search_types import Search


def endpoint(u,v,label):
    su,hu,sv,hv=label
    return (transform(u+su,extreme_tail(state_of(u+su),hu)[0])+
            transform(v+sv,extreme_tail(state_of(v+sv),hv)[0]))


def node_interval(node):
    return (endpoint(node['left'],node['right'],node['lower']),
            endpoint(node['left'],node['right'],node['upper']))


def type_of(node):
    u,v=node['left'],node['right']
    kind='full' if node_interval(node)==hull(u,v) else [node['lower'],node['upper']]
    return {'states':[state_of(u),state_of(v)],'parities':[len(u)%2,len(v)%2],
            'endpoints':kind}


class Builder:
    def __init__(self,search):
        self.search=search;self.nodes=[];self.memo={}

    def label(self,u,v,z):
        return min(self.search.pool(u,v),key=lambda e:abs(e[0]-z))[1]

    def build(self,u,v,lo_label,hi_label,depth):
        key=(u,v,tuple(lo_label),tuple(hi_label),depth)
        if key in self.memo:return self.memo[key]
        index=len(self.nodes);self.memo[key]=index
        node={'left':u,'right':v,'lower':lo_label,'upper':hi_label,
              'remaining_depth':depth,'children':[]}
        self.nodes.append(node)
        lo,hi=node_interval(node)
        if not depth:
            if (lo,hi)!=hull(u,v):raise AssertionError('leaf must be a full hull')
            return index
        offers=[]
        for uu,vv,_,_ in self.search.children(u,v):
            cost=len(uu)+len(vv)-len(u)-len(v) if getattr(self.search,'digit_budget',False) else 1
            child_depth=max(0,depth-cost)
            if hasattr(self.search,'options'):
                labels=[(c[2],c[3]) for c in self.search.options(uu,vv,child_depth)]
            else:
                labels=[(self.label(uu,vv,aa),self.label(uu,vv,bb))
                        for aa,bb in self.search.domain(uu,vv,child_depth)]
            for lab_a,lab_b in labels:
                ea,eb=endpoint(uu,vv,lab_a),endpoint(uu,vv,lab_b)
                offers.append((ea,eb,uu,vv,lab_a,lab_b))
        offers.sort()
        current=lo;i=0
        while current<hi:
            best=None
            while i<len(offers) and offers[i][0]<=current:
                if best is None or offers[i][1]>best[1]:best=offers[i]
                i+=1
            if best is None or best[1]<=current:
                raise AssertionError(f'floating discovery failed exact cover at {u}|{v}, depth {depth}')
            _,end,uu,vv,a,b=best
            cost=len(uu)+len(vv)-len(u)-len(v) if getattr(self.search,'digit_budget',False) else 1
            node['children'].append(self.build(uu,vv,a,b,max(0,depth-cost)))
            current=end
        return index

    def root(self,u,v,depth):
        lo,hi=self.search.parameters(u,v)[-2]
        a,b=self.label(u,v,lo),self.label(u,v,hi)
        if (endpoint(u,v,a),endpoint(u,v,b))!=hull(u,v):
            raise AssertionError('endpoint menu misses root extrema')
        return self.build(u,v,a,b,depth)


def verify(data):
    """Replay without invoking the floating-point Search or its decisions."""
    nodes=data['nodes'];bound=F(str(data['ratio_bound']))
    assert bound>1 and data['roots']
    max_step=data.get('max_step',1)
    assert max_step in (1,2)
    horizon_unit=data.get('horizon_unit','steps')
    assert horizon_unit in ('steps','digits')
    bank=data.get('shape_bank')
    if bank is not None:
        from search_shape_bank import SHAPES,SHAPES8,reflect
        assert bank in (4,8)
        patterns=SHAPES if bank==4 else SHAPES8
    reached=set()
    def visit(i):
        if i in reached:return
        reached.add(i);n=nodes[i];u,v=n['left'],n['right']
        lo,hi=node_interval(n)
        assert lo<hi
        assert isinstance(n['remaining_depth'],int) and n['remaining_depth']>=0
        if bank is not None and (lo,hi)!=hull(u,v):
            labels=(tuple(n['lower']),tuple(n['upper']))
            assert any(labels in ((a,b),(b,a),(reflect(a),reflect(b)),(reflect(b),reflect(a)))
                       for a,b in patterns)
        assert F(1,bound)<=restricted_ratio(u,v)<=bound
        if n['remaining_depth']==0:
            assert not n['children'] and (lo,hi)==hull(u,v)
            return
        assert n['children']
        intervals=[]
        for j in n['children']:
            c=nodes[j];uu,vv=c['left'],c['right']
            assert uu.startswith(u) and vv.startswith(v)
            du,dv=uu[len(u):],vv[len(v):]
            assert 1<=len(du)+len(dv)<=max_step and all(x in '123' for x in du+dv)
            cost=len(du)+len(dv) if horizon_unit=='digits' else 1
            assert c['remaining_depth']==max(0,n['remaining_depth']-cost)
            state_of(uu);state_of(vv)
            visit(j);intervals.append(node_interval(c))
        assert any(a<=lo and hi<=b for a,b in merge(intervals))
    for r in data['roots']:
        root=nodes[r]
        assert root['remaining_depth']==data['depth']
        assert node_interval(root)==hull(root['left'],root['right'])
        visit(r)
    assert len(reached)==len(nodes)
    return {'verified_nodes':len(nodes),'verified_edges':sum(len(n['children']) for n in nodes),
            'unproved_full_hull_leaves':sum(n['remaining_depth']==0 for n in nodes),
            'distinct_types':len({json.dumps(type_of(n),sort_keys=True) for n in nodes})}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=6)
    ap.add_argument('--n-max',type=int,default=2)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--verify',type=Path)
    ap.add_argument('--bank',type=int,choices=(4,8))
    ap.add_argument('--max-step',type=int,choices=(1,2),default=1)
    args=ap.parse_args()
    if args.verify:
        print(json.dumps(verify(json.loads(args.verify.read_text())),indent=2));return
    if args.bank:
        from search_shape_bank import ShapeSearch,SHAPES,SHAPES8
        search=ShapeSearch(shapes=SHAPES if args.bank==4 else SHAPES8,max_step=args.max_step)
    else:
        if args.max_step!=1:ap.error('--max-step 2 requires --bank')
        search=Search(1,20)
    builder=Builder(search);roots=[]
    for n in range(args.n_max+1):
        u,v='3211'+'313121'*n+'3','4322'+'313121'*n
        roots.append(builder.root(u,v,args.depth))
    data={'status':'exact finite refinement certificate with UNPROVED full-hull leaves',
          'ratio_bound':20,'menu_depth':1,'depth':args.depth,
          'max_step':args.max_step,'shape_bank':args.bank,
          'horizon_unit':'digits' if getattr(search,'digit_budget',False) else 'steps',
          'roots':roots,'nodes':builder.nodes}
    data['verification']=verify(data)
    data['root_covers']=[]
    for i in roots:
        root=data['nodes'][i];u,v=root['left'],root['right']
        data['root_covers'].append([
            {'left_suffix':data['nodes'][j]['left'][len(u):],
             'right_suffix':data['nodes'][j]['right'][len(v):],
             'type':type_of(data['nodes'][j])}
            for j in root['children']])
    print(json.dumps({'verification':data['verification'],'root_covers':data['root_covers']},indent=2))
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
