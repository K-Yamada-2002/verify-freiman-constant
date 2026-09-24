#!/usr/bin/env python3
"""Generate new legal successor maps and exact arrival-box covers for repairs."""
import argparse
from itertools import product
import json
import math
from pathlib import Path

from exact import F,state_of
from anchored_geometry import B,transition
from verify_scalar_graph import ScalarVerifier


def add_moves(data, parents, length=3, memory=7, refinement=3):
    base = F(str(data['settings']['base']))
    bins = data['settings']['bins']
    keys = {}
    next_id = -1
    count = max((-r['source_rule'] for r in data['rules'] if r['source_rule'] < 0),default=0)
    for parent in parents:
        node = data['nodes'][str(parent)]
        checker = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',settings=data['settings'],nodes=[node]))
        words = []
        for state in node['states']:
            family = ['']
            for n in range(1,length+1):
                for digits in product('123',repeat=n):
                    w = ''.join(digits)
                    try:
                        state_of(state+w)
                    except ValueError:
                        continue
                    family.append(w)
            words.append(family)
        existing = {tuple(e['suffixes']) for r in data['rules'] if r['parent'] == parent for e in r['children']}
        for u in words[0]:
            for v in words[1]:
                if not 0 < len(u)+len(v) <= length or (u,v) in existing:
                    continue
                r,s,h,p = transition(u,v,*checker.box(0),node['parity'])
                requests = []
                if h[0] <= 1:
                    requests.append((False,(h[0],min(h[1],B(1)))))
                if h[1] > 1:
                    requests.append((True,(1/h[1],min(1/h[0],B(1)))))
                if any(lo < base**bins for _,(lo,hi) in requests):
                    continue
                edge = dict(suffixes=[u,v],cases=[])
                for swap,(lo,hi) in requests:
                    states = [(node['states'][0]+u)[-memory:],(node['states'][1]+v)[-memory:]]
                    if swap:
                        states.reverse()
                    # Floats bound the candidate index range with padding;
                    # the selected cells are tested with exact inequalities.
                    q0 = max(0,int(math.log(float(B.coerce(hi).decimal()))/math.log(float(base)))-2)
                    q1 = min(bins-1,int(math.log(float(B.coerce(lo).decimal()))/math.log(float(base)))+2)
                    lo_float,hi_float = float(B.coerce(lo).decimal()),float(B.coerce(hi).decimal())
                    destinations = []
                    intervals = []
                    for q in range(q0,q1+1):
                        left,right = base**(q+1),base**q
                        width = (right-left)/2**refinement
                        # Bound cell indices numerically, then retain only
                        # exact intersections and verify the entire cover.
                        part0 = max(0,math.floor((lo_float-float(left))/float(width))-2)
                        part1 = min(2**refinement-1,
                                    math.floor((hi_float-float(left))/float(width))+2)
                        for part in range(part0,part1+1):
                            a,b = left+part*width,left+(part+1)*width
                            if b < lo or hi < a or (lo < hi and (b == lo or hi == a)):
                                continue
                            key = tuple(states),p,q,part
                            if key not in keys:
                                while str(next_id) in data['nodes']:
                                    next_id -= 1
                                keys[key] = next_id
                                data['nodes'][str(next_id)] = dict(id=next_id,states=states,parity=p,
                                    ratio_bin=q,ratio_refinement=[refinement,part],
                                    interval=[-data['settings']['grid'],data['settings']['grid']],
                                    covered=False,children=[])
                                next_id -= 1
                            destinations.append(keys[key])
                            intervals.append((a,b))
                    checker.covers_ratio((lo,hi),intervals)
                    edge['cases'].append(dict(swap=swap,interval=[-data['settings']['grid'],data['settings']['grid']],
                                             destinations=destinations))
                count += 1
                data['rules'].append(dict(parent=parent,children=[edge],source_rule=-count))
        print(json.dumps(dict(parent=parent,new_moves=count,new_boxes=len(keys))),flush=True)
    data['generated_moves'] = dict(count=count,boxes=sum(int(i)<0 for i in data['nodes']),total_length=length,memory=memory,
                                   ratio_refinement=refinement,scope='new intervals assigned only with --expand-offers')
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('incoming',type=Path)
    ap.add_argument('--parents',type=int,nargs='+',required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--length',type=int,default=3)
    args = ap.parse_args()
    data = add_moves(json.loads(args.incoming.read_text()),args.parents,args.length)
    args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__ == '__main__':
    main()
