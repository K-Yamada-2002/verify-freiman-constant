#!/usr/bin/env python3
"""Restrict a scalar root to a smaller box containing an exact physical seed.

Existing rules are discarded: a seed and a smaller box prove no filling.
"""
import argparse
import copy
import json
from pathlib import Path

from anchored_geometry import parameters
from verify_scalar_graph import ScalarVerifier


def refine(data, prefixes, memory, refinement):
    if not 2 <= memory or not 0 <= refinement <= 16:
        raise ValueError('invalid refinement settings')
    result = copy.deepcopy(data)
    old = ScalarVerifier(result)
    root = result['roots'][0]
    result['root_prefixes'] = prefixes
    old.seed()
    box = old.box(root)
    node = copy.deepcopy(result['nodes'][root])
    # Leave a nonempty preceding prefix so shape_box's starting domain applies.
    node.update(id=0,states=[w[-min(memory,len(w)-1):] for w in prefixes],covered=False,children=[])
    h = parameters(*prefixes)[2]
    node.pop('ratio_refinement',None)
    result.update(nodes=[node],roots=[0],closed_candidate=False,open_nodes=1,
                  status='refined physical seed; filling obligation open')
    result['settings']['memory'] = memory
    basebox = ScalarVerifier(result).box(0)[2]
    width = (basebox[1]-basebox[0])/2**refinement
    part = next(i for i in range(2**refinement) if basebox[0]+i*width <= h <= basebox[0]+(i+1)*width)
    node['ratio_refinement'] = [refinement,part]
    checker = ScalarVerifier(result)
    if not all(a <= c <= d <= b for (a,b),(c,d) in zip(box,checker.box(0))):
        raise ValueError('requested seed box is not a refinement of the old box')
    checker.check_initial_hull(0)
    interval = checker.seed()
    return result,dict(prefixes=prefixes,physical_interval=interval,closed=False,
                       box_widths=[str(b-a) for a,b in checker.box(0)])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--seed',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--memory',type=int,default=8)
    ap.add_argument('--refinement',type=int,default=6)
    args = ap.parse_args()
    data,report = refine(json.loads(args.graph.read_text()),json.loads(args.seed.read_text())['prefixes'],
                         args.memory,args.refinement)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    args.output.with_suffix('.seed.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
