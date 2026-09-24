#!/usr/bin/env python3
"""Reproducible exact finite-distance cover of the ten candidate intervals.

Tail bounds use Fraction arithmetic; the C++ search uses outward integer
rounding. No floating-point decisions are involved. This is not an inclusion
proof. Every legal cylinder has an infinite periodic-2 continuation.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from search import Model
from target_cover import ThresholdModel
from reduce_cover import same_language

ROOT=Path(__file__).resolve().parent
S=10**15

def prepare(definition,claim):
    m=Model(definition['label'],definition['alphabet'],definition['forbidden'])
    spec=definition['model']
    old=ThresholdModel(spec['digits'],spec['radius'],Q(spec['threshold']))
    equivalent, pairs=same_language(m,old)
    if not equivalent: raise ValueError('Language mismatch')
    bounds=m.tail_bounds(Q,40)
    ids={s:i for i,s in enumerate(m.states)}
    target=[(Q(str(x))-3)*S for x in claim['target']]
    assert all(x.denominator==1 for x in target)
    rows=[f'{len(ids)} {int(target[0])} {int(target[1])}']
    for s in m.states:
        lo,hi=bounds[s]
        low=(lo*S).numerator//(lo*S).denominator
        high=-(-(hi*S).numerator//(hi*S).denominator)
        es=dict(m.edges[s])
        rows.append(' '.join(map(str,[low,high]+[ids[es[k]] if k in es else -1 for k in '123'])))
    for side in ('left','right'):
        rows.append(str(len(claim[side])))
        rows.extend(claim[side])
    return '\n'.join(rows)+'\n',pairs

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--exponent',type=int,default=8)
    ap.add_argument('--claims',type=int,nargs='*',default=list(range(1,11)))
    ap.add_argument('--budget',type=int,default=2000000000)
    ap.add_argument('--output',type=Path,default=ROOT/'refined_cover.json')
    args=ap.parse_args()
    source=ROOT/'reduced_ten.json'; audit=ROOT/'reduced_ten_audit.json'
    claims=json.loads(source.read_text())['claims']
    definitions={d['graph']:d for d in json.loads(audit.read_text())['definitions']}
    result={'meaning':'For every x in each target I, distance(x,K+L) <= 10^(-exponent). Does NOT prove I subset K+L.',
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'cpp_sha256':hashlib.sha256((ROOT/'refine_cover.cpp').read_bytes()).hexdigest(),
            'claims':[]}
    with tempfile.TemporaryDirectory(prefix='refine-cover-') as tmp:
        exe=Path(tmp)/'cover'
        subprocess.run(['c++','-O3','-std=c++17',str(ROOT/'refine_cover.cpp'),'-o',str(exe)],check=True)
        for number in args.claims:
            c=claims[number-1]
            inp,pairs=prepare(definitions[c['graph']],c)
            run=subprocess.run([str(exe),str(args.exponent),str(args.budget)],input=inp,text=True,capture_output=True,check=True)
            r=json.loads(run.stdout)
            r.update(claim=number,left=c['left'],right=c['right'],language_state_pairs=pairs,
                     target_sum=[str(Q(str(x))-3) for x in c['target']],input_sha256=hashlib.sha256(inp.encode()).hexdigest())
            result['claims'].append(r)
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            print(number,r['covers_target'],r['complete'],r['visited'],r['seconds'],flush=True)
if __name__=='__main__':main()
