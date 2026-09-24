#!/usr/bin/env python3
"""Static size inventory, not a positivity verifier or operation benchmark."""
from pathlib import Path
from fractions import Fraction
import json,re
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'Freiman_Hall_ray_verification/certificates'
result={}
for family in ('section14','section15_early'):
    rows=[]
    for f in sorted((BASE/family).rglob('geometry_*.json')):
        d=json.loads(f.read_text()); kinds={}; deepest=0
        def walk(t,depth=0):
            global deepest
            deepest=max(deepest,depth)
            if 'split' in t:
                kinds['split']=kinds.get('split',0)+1
                for c in t['children']:walk(c,depth+1)
            else:
                k='pair' if 'pair' in t else 'diagonal' if 'diagonal' in t else 'unknown'
                kinds[k]=kinds.get(k,0)+1
        for t in d['proofs']:walk(t)
        bitmax=0
        def bits(v):
            global bitmax
            if isinstance(v,list):
                for x in v:bits(x)
            elif isinstance(v,str) and re.fullmatch(r'-?\d+(?:/\d+)?',v):
                q=Fraction(v);bitmax=max(bitmax,abs(q.numerator).bit_length(),q.denominator.bit_length())
        bits(d['thresholds'])
        rows.append(dict(file=f.name,records=len(d['records']),proofs=len(d['proofs']),
                         tree_nodes=kinds,max_split_depth=deepest,input_rational_max_bits=bitmax,
                         open_obligations=len(d['open_geometry'])))
    result[family]=dict(files=rows,records=sum(r['records'] for r in rows),
        proofs=sum(r['proofs'] for r in rows),
        max_split_depth=max(r['max_split_depth'] for r in rows),
        input_rational_max_bits=max(r['input_rational_max_bits'] for r in rows))
result['scope']='Two local geometry families only. Input coefficient sizes do not bound intermediate arithmetic or total verification cost.'
(HERE/'certificate_sizes.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:{a:b for a,b in v.items() if a!='files'} if isinstance(v,dict) else v for k,v in result.items()},indent=2))
