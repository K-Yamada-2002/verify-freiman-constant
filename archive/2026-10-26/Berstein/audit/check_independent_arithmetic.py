"""Reproducible exact-Fraction checks of the independent C++ arithmetic.

Finite regression checks supplement the mathematical audit.
The actual independent C++ source is compiled into a temporary harness.
"""

import hashlib
import json
import random
import subprocess
import tempfile
from fractions import Fraction as Q
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if not __debug__:
    raise RuntimeError('Run without -O: assertion checks are required')
D=1<<48
rng=random.Random(313134314)
requests=[]
expected=[]

def floor(x): return x.numerator//x.denominator
def ceil(x): return -floor(-x)

for operation in ('p','q'):
    for _ in range(1000):
        a=sorted(rng.randint(-10*D,10*D) for _ in range(2))
        b=sorted(rng.randint(D//10,3*D) if operation=='q' else rng.randint(-10*D,10*D) for _ in range(2))
        values=[Q(x*y,D) if operation=='p' else Q(x*D,y) for x in a for y in b]
        requests.append(' '.join(map(str,[operation,*a,*b])))
        expected.append(('exact',(floor(min(values)),ceil(max(values)))))

for _ in range(1000):
    values=[Q(rng.randint(-100,100),rng.randint(1,100)) for _ in range(4)]
    ids=[rng.randrange(4) for _ in range(4)]
    t,u=rng.randint(0,D),rng.randint(0,D)
    ranges=[]
    for i in range(4):
        for j in range(4):
            x=D*(values[i]-values[j])
            ranges.extend((floor(x)-rng.randrange(4),ceil(x)+rng.randrange(4)))
    requests.append(' '.join(map(str,['t',*ids,t,u,*ranges])))
    exact=(D-t)*values[ids[0]]+t*values[ids[1]]-(D-u)*values[ids[2]]-u*values[ids[3]]
    expected.append(('transport',exact))

base=Q(51,50)
for _ in range(1000):
    parent=rng.randrange(310)
    left=sorted(rng.randint(D//2,2*D) for _ in range(2))
    right=sorted(rng.randint(D//2,2*D) for _ in range(2))
    requests.append(' '.join(map(str,['b',parent,*left,*right])))
    image=(base**(parent-155)*Q(right[0],left[1]),base**(parent+1-155)*Q(right[1],left[0]))
    expected.append(('bins',image))

with tempfile.TemporaryDirectory(prefix='berstein-arithmetic-audit-') as temporary:
    binary=Path(temporary)/'harness'
    subprocess.run(['c++','-std=c++17','-O2','-fsanitize=undefined','-fno-sanitize-recover=all',str(Path(__file__).with_name('arithmetic_harness.cpp')),'-o',str(binary)],check=True)
    result=subprocess.run([str(binary),str(ROOT/'Freiman/data/graph_wide.dat'),str(ROOT/'Freiman/data/graph_wide.json.alive.bin')],input='\n'.join(requests)+'\n',text=True,capture_output=True,check=True)
answers=result.stdout.splitlines()
assert len(answers)==len(expected)
accepted=0
for answer,(kind,value) in zip(answers,expected):
    integers=tuple(map(int,answer.split()))
    if kind=='exact':
        assert integers==value,(kind,integers,value)
    elif kind=='transport':
        assert integers[0]<=value<=integers[1],(kind,integers,value)
    else:
        ok,first,last=integers
        if ok:
            assert 0<=first<=last<310
            assert base**(first-155)<=value[0]<=value[1]<=base**(last+1-155),(kind,integers,value)
            accepted+=1

source=ROOT/'Berstein/audit/independent_kernel.cpp'
report=dict(passed=True,seed=313134314,multiplication_exact_rounding_cases=1000,division_exact_rounding_cases=1000,endpoint_transport_enclosure_cases=1000,mapped_bin_cases=1000,mapped_bin_accepted_and_covered=accepted,cpp_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),limitation='Finite randomized regression checks supplement the mathematical audit; they do not prove all inputs.')
Path(__file__).with_name('independent_arithmetic.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
