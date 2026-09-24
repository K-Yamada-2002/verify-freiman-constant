#!/usr/bin/env python3
"""Uniform local covers for actual children of the periodic initial family.

The variable n>=1 is encoded by x in [0,1/85]. n=0 is checked separately.
Children are NOT asserted to be recursively filled by these local checks.
"""
from fractions import Fraction as F
from functools import lru_cache
import argparse,json
from pathlib import Path
from explore import *
from uniform_initial_cover import mul,params
from invariant_boxes import endpoints,minimum_difference,suffix_state,TYPE_LABELS
from search_shape_bank import ShapeSearch,SHAPES,SHAPES8


def word_pair(u,v,n=1):return '3211'+'313121'*n+'3'+u,'4322'+'313121'*n+v


@lru_cache(None)
def parameter_domains(u,v):
    values=[]
    for x in (F(0),F(1,85)):
        mp=(14-x,F(19),F(53),72-x)
        left=mul(mul(mul(matrix('3211'),mp),matrix('3')),matrix(u))
        right=mul(mul(matrix('4322'),mp),matrix(v))
        assert all(a>0 for a in left+right)
        values.append(params(left,right))
    box=tuple((min(a,b),max(a,b)) for a,b in zip(*values))
    a,b=word_pair(u,v,0);point=params(matrix(a),matrix(b))
    return (tuple((x,x) for x in point),box)


def kind_id(name):
    if name=='full':return 0
    return 2*int(name[1])-1+name.endswith('R')


def kind_name(kind):return 'full' if kind==0 else f'J{(kind+1)//2}'+('R' if kind%2==0 else '')


def minimum_all(a,b,domains,p):
    return min(minimum_difference(a,b,*domain,p,exact=True) for domain in domains)


def sorted_endpoint_pair(pair,domains,p):
    if minimum_all(pair[1],pair[0],domains,p)>=0:return pair
    if minimum_all(pair[0],pair[1],domains,p)>=0:return pair[::-1]
    return None


def geometric_cover(u,v,kind,search,lookahead=4,include_n0=True):
    left,right=word_pair(u,v)
    s,t=suffix_state(left),suffix_state(right);p=(-1)**(len(left)+len(right))
    domains=parameter_domains(u,v)
    if not include_n0:domains=domains[1:]
    parent=sorted_endpoint_pair(endpoints(s,t,p,kind),domains,p)
    if parent is None:return None
    center=[sum(x)/2 for x in domains[-1]]
    def point(pair):
        r,ss,q=map(float,center);x,y=map(lambda a:float(a.decimal()),pair)
        return x/(1+r*x)+p*q*y/(1+ss*y)
    offers=[]
    for a,b,_,_ in search.children(left,right):
        du,dv=a[len(left):],b[len(right):]
        for candidate in search.options(a,b,lookahead):
            k=kind_id(candidate[4]);ep=endpoints(s,t,p,k,du,dv)
            if ep is None:continue
            ordered=sorted_endpoint_pair(ep,domains,p)
            if ordered is not None:
                offers.append({'suffixes':(du,dv),'kind':k,'endpoints':ordered,
                               'upper_mid':point(ordered[1])})
    current=parent[0];last=point(current);chain=[];obligations=[]
    while minimum_all(current,parent[1],domains,p)<0:
        choices=[]
        for o in offers:
            if o['upper_mid']<=last+1e-13:continue
            if minimum_all(o['endpoints'][1],current,domains,p)<0:continue
            lower=minimum_all(current,o['endpoints'][0],domains,p)
            if lower>=0:choices.append((o['upper_mid'],o,lower))
        if not choices:return None
        _,o,lower=max(choices,key=lambda a:a[0])
        chain.append({'suffixes':o['suffixes'],'kind':o['kind'],'name':kind_name(o['kind'])})
        obligations.append(lower.record());current=o['endpoints'][1];last=o['upper_mid']
    obligations.append(minimum_all(current,parent[1],domains,p).record())
    return {'left_suffix':u,'right_suffix':v,'kind':kind,'name':kind_name(kind),
            'n_range':'all n>=0' if include_n0 else 'all n>=1',
            'domains':[[[str(a),str(b)] for a,b in d] for d in domains],
            'children':chain,'contact_lower_bounds':obligations}


def verify_row(row):
    u,v,k=row['left_suffix'],row['right_suffix'],row['kind']
    domains=parameter_domains(u,v)
    if row['n_range']=='all n>=1':domains=domains[1:]
    assert row['domains']==[[[str(a),str(b)] for a,b in d] for d in domains]
    left,right=word_pair(u,v);s,t=suffix_state(left),suffix_state(right)
    p=(-1)**(len(left)+len(right))
    parent=sorted_endpoint_pair(endpoints(s,t,p,k),domains,p)
    assert parent is not None
    current=parent[0]
    for child in row['children']:
        du,dv=child['suffixes']
        assert 1<=len(du)+len(dv)<=2
        assert all(a in '123' for a in du+dv)
        ep=endpoints(s,t,p,child['kind'],du,dv)
        assert ep is not None
        ep=sorted_endpoint_pair(ep,domains,p);assert ep is not None
        assert minimum_all(current,ep[0],domains,p)>=0
        assert minimum_all(ep[1],current,domains,p)>=0
        current=ep[1]
    assert minimum_all(current,parent[1],domains,p)>=0


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lookahead',type=int,default=4)
    ap.add_argument('--layers',type=int,default=1)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--verify',type=Path)
    ap.add_argument('--bank',type=int,choices=(4,8),default=4)
    ap.add_argument('--focus',nargs=3,metavar=('LEFT_SUFFIX','RIGHT_SUFFIX','KIND_ID'))
    args=ap.parse_args()
    if args.verify:
        data=json.loads(args.verify.read_text())
        for row in data['covers']:verify_row(row)
        print('verified',len(data['covers']),'uniform local covers; frontier remains unproved');return
    search=ShapeSearch(max_step=2,shapes=SHAPES if args.bank==4 else SHAPES8)
    frontier=[('1','',0),('2','',0),('','1',4)];done={};failed=[]
    if args.focus:frontier=[(args.focus[0],args.focus[1],int(args.focus[2]))]
    for layer in range(args.layers):
        new=[]
        for u,v,k in frontier:
            if (u,v,k) in done:continue
            row=geometric_cover(u,v,k,search,args.lookahead)
            if row is None:row=geometric_cover(u,v,k,search,args.lookahead,False)
            if row is None:
                failed.append((u,v,k));print('FAILED',u,v,k,flush=True);continue
            verify_row(row);done[(u,v,k)]=row
            print('covered',u or '-',v or '-',kind_name(k),row['n_range'],
                  [(a['suffixes'],a['name']) for a in row['children']],flush=True)
            new.extend((u+a['suffixes'][0],v+a['suffixes'][1],a['kind']) for a in row['children'])
        frontier=list(dict.fromkeys(new))
    data={'status':'exact uniform LOCAL covers, not a closed induction',
          'shape_bank':args.bank,
          'lookahead_used_only_for_discovery':args.lookahead,'covers':list(done.values()),
          'failed_searches':failed,'unproved_frontier':[x for x in frontier if x not in done]}
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
