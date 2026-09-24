#!/usr/bin/env python3
"""Transfer saved rules to specialized types, replaying every whole rule."""
import argparse,copy,json
from collections import defaultdict
from pathlib import Path
from chart_geometry import Domain
from type_graph_geometry import endpoint
from verify_piecewise_charts import PiecewiseVerifier
from chart_strategy_ranks import report

def signature(graph,index):
    n=graph['nodes'][index];d=Domain.read(graph['cells'][n['cell']])
    return (d.words,d.high,d.base.states,d.base.parity,d.base.high,
            endpoint(d.states,n['lower']),endpoint(d.states,n['upper']))

def transfer(target,source,indices):
    graph=copy.deepcopy(target);checker=PiecewiseVerifier(graph);lookup=defaultdict(list)
    for i in range(len(graph['nodes'])):lookup[signature(graph,i)].append(i)
    rows=[]
    for i in indices:
        n=source['nodes'][i]
        if not n.get('children') or n.get('pieces'):raise ValueError('ordinary source rule required')
        for j in lookup[signature(source,i)]:
            if graph['nodes'][j].get('children') or graph['nodes'][j].get('pieces'):continue
            edges=copy.deepcopy(n['children']);missing=False
            for edge in edges:
                destinations=[]
                for d in edge['destinations']:
                    destinations.extend(dict(node=k,swap=d['swap']) for k in lookup[signature(source,d['node'])])
                if not destinations:missing=True;break
                edge['destinations']=[dict(node=k,swap=s) for k,s in sorted({(d['node'],d['swap']) for d in destinations})]
            if missing:
                rows.append(dict(source=i,target=j,accepted=False,reason='no retained destinations'));continue
            old=copy.deepcopy(graph['nodes'][j]);graph['nodes'][j]['children']=edges
            try:check=checker.local(j)
            except ValueError as error:
                graph['nodes'][j]=old;checker.checked.pop(j,None)
                rows.append(dict(source=i,target=j,accepted=False,reason=str(error)))
            else:rows.append(dict(source=i,target=j,accepted=True,verification=check))
    audit=checker.audit()
    if audit['failed_rules']:raise ValueError('transferred graph failed audit')
    return graph,dict(rows=rows,ranks=report(graph)),audit

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('target',type=Path);ap.add_argument('source',type=Path)
    ap.add_argument('--nodes',type=int,nargs='+',required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    graph,summary,audit=transfer(json.loads(args.target.read_text()),json.loads(args.source.read_text()),args.nodes)
    for path,data in [(args.output,graph),(args.output.with_suffix('.report.json'),summary),(args.output.with_suffix('.audit.json'),audit)]:
        path.write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps(summary),flush=True)
if __name__=='__main__':main()
