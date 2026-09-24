#!/usr/bin/env python3
"""Compare all compressed-DAG paths to the separate original word enumerator.

Extract only its pure enumeration function, avoiding imports of numeric engines.
The original function's seven-step rejection remains active.
"""
import ast, hashlib, itertools, json
from pathlib import Path
from check_history_dag import certificate, need

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'Freiman_Hall_ray_verification/verification/families/target_selection/verify_suffix_targets_independent.py'
source=SOURCE.read_bytes()
tree=ast.parse(source)
fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='enumerate_histories')
env={'product':itertools.product,'need':need}
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(SOURCE),'exec'),env)
data=certificate();nodes=data['nodes']
results={}
for kind in ('left','right','mixed','rightmixed'):
    compressed=set()
    for ctx,w in itertools.product(('1','2','3','31','313','3131'),(0,1)):
        stack=[(data['roots'][w],())]
        while stack:
            i,path=stack.pop()
            _,mark,p0,p1,wide,_=nodes[i]['state']
            wanted_par=(1,0) if kind in ('mixed','rightmixed') else (0,0)
            wanted_wide=0 if kind in ('right','rightmixed') else 1
            if mark=='3131' and (p0,p1)==wanted_par and wide==wanted_wide:
                compressed.add((ctx,w,path))
            for edge in nodes[i]['edges']:
                a,b,reflect=edge['label']
                stack.append((edge['target'],path+(((a,b),reflect),)))
    original=set(env['enumerate_histories'](kind))
    need(compressed==original,'complete path equality '+kind)
    results[kind]=len(original)
out=dict(status='PASS',source_sha256=hashlib.sha256(source).hexdigest(),
         check='Exact path-set equality, not just counts',histories=results)
(HERE/'history_crosscheck.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
