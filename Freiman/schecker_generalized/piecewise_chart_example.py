#!/usr/bin/env python3
"""Exact example: guarded choices work, each saved uniform choice fails."""
import argparse
import copy
from itertools import product
import json
from pathlib import Path

from chart_geometry import Domain, compare, relative_box
from type_graph_geometry import Cell, decode, encode, endpoint, require
from verify_piecewise_charts import PiecewiseVerifier
from verify_cyclic_types import contains_box


def point_domain(domain, point):
    b=domain.base
    require(all(lo<=x<=hi for (lo,hi),x in zip((b.r,b.s,b.ratio),point)), 'sample outside base box')
    return Domain(Cell(b.states,b.parity,b.high,*((x,x) for x in point)),domain.words,domain.high)


def obstruction(checker, piece, point, edge_index, kind):
    node,domain,low,_=checker.node(0)
    actual=point_domain(domain,point)
    edges=node['pieces'][piece]['children']
    edge=edges[edge_index]
    if kind=='contact':
        prev=edges[edge_index-1] if edge_index else None
        current=endpoint(domain.states,prev['upper'],prev['suffixes']) if prev else low
        lower=endpoint(domain.states,edge['lower'],edge['suffixes'])
        return compare(actual,lower,current,strict=True)
    require(kind=='destination','unknown obstruction kind')
    child=actual.extend(*edge['suffixes'],edge['high'])
    for d in edge['destinations']:
        target=checker.cells[checker.nodes[d['node']]['cell']]
        image=relative_box(child.exchange() if d['swap'] else child,target)
        if image is not None and all(contains_box(a,b) for a,b in zip(
                (target.base.r,target.base.s,target.base.ratio),(image.r,image.s,image.ratio))):
            return False
    return True


def verify(record):
    checker=PiecewiseVerifier(record['certificate'])
    result=checker.local(0)
    require(len(record['uniform_failures'])==len(checker.nodes[0]['pieces']), 'missing uniform-choice checks')
    for i,row in enumerate(record['uniform_failures']):
        require(obstruction(checker,i,tuple(map(decode,row['base_parameters'])),row['edge'],row['kind']),
                'purported uniform-choice obstruction is false')
    return dict(status='guarded local implication verified; every saved uniform choice has an exact obstruction',
                pieces=result['parameter_pieces'],unproved_dependencies=result['dependencies'])


def extract(data,index):
    original=PiecewiseVerifier(data);original.local(index)
    parent=data['nodes'][index]
    chosen=list(dict.fromkeys([index]+[d['node'] for p in parent['pieces'] for e in p['children'] for d in e['destinations']]))
    ids={j:i for i,j in enumerate(chosen)}
    used=sorted({data['nodes'][j]['cell'] for j in chosen}|{p['cell'] for p in parent['pieces']})
    cids={j:i for i,j in enumerate(used)}
    nodes=[]
    for j in chosen:
        node=copy.deepcopy(data['nodes'][j]);node['cell']=cids[node['cell']]
        if j!=index:
            node.pop('pieces',None);node['children']=[]
        else:
            for p in node['pieces']:
                p['cell']=cids[p['cell']]
                for e in p['children']:
                    for d in e['destinations']:
                        d['node']=ids[d['node']]
        nodes.append(node)
    cert=dict(format=data['format'],cells=[data['cells'][j] for j in used],nodes=nodes,roots={})
    checker=PiecewiseVerifier(cert);base=checker.cells[nodes[0]['cell']].base
    points=list(product(*[(lo,(lo+hi)/2,hi) for lo,hi in (base.r,base.s,base.ratio)]))
    failures=[]
    for i,p in enumerate(nodes[0]['pieces']):
        found=None
        for kind in ('contact','destination'):
            for e in range(len(p['children'])):
                for point in points:
                    if obstruction(checker,i,point,e,kind):
                        found=dict(kind=kind,edge=e,base_parameters=list(map(encode,point)))
                        break
                if found:break
            if found:break
        require(found is not None,'no exact obstruction found for a uniform choice')
        failures.append(found)
    result=dict(source_proof_hash=original.proof_hash(),source_node=index,certificate=cert,uniform_failures=failures)
    result['verification']=verify(result)
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--graph',type=Path)
    ap.add_argument('--node',type=int)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--verify',type=Path)
    args=ap.parse_args()
    if args.verify:
        result=verify(json.loads(args.verify.read_text()))
    else:
        if args.graph is None or args.node is None or args.output is None:
            ap.error('creation requires graph, node and output')
        record=extract(json.loads(args.graph.read_text()),args.node)
        args.output.write_text(json.dumps(record,indent=2)+'\n')
        result=record['verification']
    print(json.dumps(result))


if __name__=='__main__':
    main()
