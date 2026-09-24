#!/usr/bin/env python3
"""Count exact field operations of the independent checker; not a CPU model."""
from pathlib import Path
from fractions import Fraction as F
import json,time
import verify_uniform_restart as v
HERE=Path(__file__).resolve().parent
counts={};methods=('__add__','__radd__','__mul__','__rmul__','inv','sign')
for name in methods:
    original=getattr(v.K,name)
    def counted(self,*args,_name=name,_original=original,**kwargs):
        counts[_name]=counts.get(_name,0)+1
        return _original(self,*args,**kwargs)
    setattr(v.K,name,counted)
start=time.monotonic()
results=[v.verify_file(HERE/'uniform_periodic_strip.json',False),v.verify_file(HERE/'uniform_root_connection.json',True)]
records=[]
for name in ('uniform_periodic_strip.json','uniform_root_connection.json'):
    d=json.loads((HERE/name).read_text());records.extend(r for c in d['cases'] for r in c['records'])
coefficients=[F(s) for r in records for a in r['bernstein'] for s in a]
result=dict(status='PASS_PROFILED_INDEPENDENT_REPLAY',seconds=time.monotonic()-start,
    field_operations=counts,records=len(records),bernstein_coefficients=sum(len(r['bernstein']) for r in records),
    max_saved_coefficient_bits=max(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) for q in coefficients),
    max_coordinate_degree=max(max(r['degree']) for r in records),verified_inputs=results,
    caveat='Counts field operations of this implementation, including nested calls. Saved coefficient bits do not bound intermediate integer sizes. No historical-machine speed or memory claim.')
(HERE/'verification_cost.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:z for k,z in result.items() if k!='verified_inputs'},indent=2))
