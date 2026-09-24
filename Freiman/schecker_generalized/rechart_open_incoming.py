#!/usr/bin/env python3
"""Keep an incoming word-image as a correlated chart for an open child.

An offered interval is assigned to a new open type on the whole actual image.
Use it only if both the new type and the parent's whole child edge verify.
There are no zero-digit edges and no unproved assertion of filledness.
"""
import argparse
import copy
import json
from pathlib import Path

from chart_geometry import compare
from contract_piecewise_charts import prune, rules
from reduce_chart_frontier import counts
from type_graph_geometry import endpoint, exchange
from verify_piecewise_charts import PiecewiseVerifier


def rechart(data, targets, allow_local=False, repair_children=False, offered_only=False):
    data=copy.deepcopy(data)
    checker=PiecewiseVerifier(data)
    audit=checker.audit()
    eligible=set(range(len(data['nodes']))) if allow_local else set(audit['open_nodes'])
    if audit['failed_rules'] or not set(targets)<=eligible:
        raise ValueError('valid partial graph and open targets required')
    if set(targets)&set(data['roots'].values()):
        raise ValueError('root domains must stay unchanged')
    cache={};accepted=failed=0
    for i,node in enumerate(data['nodes'][:]):
        for rule in rules(node):
            part=checker.cells[rule['cell']]
            for edge in rule['children']:
                candidates=[d for d in edge['destinations'] if d['node'] in targets]
                for dest in candidates:
                    actual=part.extend(*edge['suffixes'],edge['high'])
                    if dest['swap']:
                        actual=actual.exchange()
                    lower=exchange(edge['lower']) if dest['swap'] else edge['lower']
                    upper=exchange(edge['upper']) if dest['swap'] else edge['upper']
                    if offered_only and not compare(actual,endpoint(actual.states,upper),
                                                    endpoint(actual.states,lower),strict=True):
                        lower,upper=upper,lower
                    key=dest['node'],actual,tuple(lower) if offered_only else (),tuple(upper) if offered_only else ()
                    if key not in cache:
                        old=data['nodes'][dest['node']]
                        if old.get('pieces') and not offered_only:
                            # Guard pullbacks require a separate exact partition.
                            cache[key]=None;failed+=1;continue
                        new=copy.deepcopy(old);new['cell']=len(checker.cells)
                        if offered_only:
                            new.update(lower=lower,upper=upper,children=[])
                            new.pop('pieces',None)
                        new['incoming_lineage']=old.get('incoming_lineage',dest['node'])
                        saved_nodes,saved_cells=len(data['nodes']),len(checker.cells)
                        checker.cells.append(actual);data['cells'].append(actual.record())
                        new_id=len(data['nodes']);data['nodes'].append(new)
                        try:
                            checker.node(new_id)
                            if new.get('children') and repair_children:
                                for outgoing in new['children']:
                                    try:
                                        checker.child(actual,outgoing)
                                    except ValueError:
                                        image=actual.extend(*outgoing['suffixes'],outgoing['high'])
                                        child_id=len(data['nodes']);cell_id=len(checker.cells)
                                        first=outgoing['destinations'][0]
                                        old_child=data['nodes'][first['node']]
                                        child_node=dict(cell=cell_id,lower=outgoing['lower'],
                                                        upper=outgoing['upper'],children=[])
                                        child_node['incoming_origins']=[dict(
                                            node=data['nodes'][d['node']].get('incoming_lineage',d['node']),
                                            swap=d['swap']) for d in outgoing['destinations']]
                                        if (not first['swap'] and child_node['lower']==old_child['lower']
                                                and child_node['upper']==old_child['upper']):
                                            child_node['incoming_lineage']=old_child.get('incoming_lineage',first['node'])
                                        checker.cells.append(image);data['cells'].append(image.record())
                                        data['nodes'].append(child_node);checker.node(child_id)
                                        outgoing['destinations']=[dict(node=child_id,swap=False)]
                            if new.get('children'):
                                checker.local(new_id)
                        except ValueError:
                            checker.checked.clear()
                            del data['nodes'][saved_nodes:];del data['cells'][saved_cells:]
                            del checker.cells[saved_cells:]
                            cache[key]=None
                        else:
                            cache[key]=new_id
                    new_id=cache[key]
                    if new_id is None:
                        failed+=1;continue
                    old=copy.deepcopy(edge['destinations'])
                    edge['destinations']=[dict(node=new_id,swap=dest['swap'])]
                    try:
                        checker.child(part,edge)
                    except ValueError:
                        edge['destinations']=old;failed+=1
                    else:
                        accepted+=1;break
    result=prune(data)
    audit=PiecewiseVerifier(result).audit()
    if audit['failed_rules']:
        raise ValueError('recharted graph failed independent audit')
    return result,dict(accepted_edges=accepted,rejected_proposals=failed,counts=counts(result)),audit


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--targets',type=int,nargs='+',required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--local',action='store_true',help='also attempt unguarded local ancestors')
    ap.add_argument('--repair-children',action='store_true',
                    help='keep exact successor images as open obligations if old routing fails')
    ap.add_argument('--offered-only',action='store_true',
                    help='replace each destination by precisely its offered interval, kept unresolved')
    args=ap.parse_args()
    source=json.loads(args.graph.read_text())
    data,summary,audit=rechart(source,set(args.targets),args.local,args.repair_children,args.offered_only)
    data['incoming_rechart']=dict(source_proof_hash=PiecewiseVerifier(source).proof_hash(),**summary)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps(summary),flush=True)


if __name__=='__main__':
    main()
