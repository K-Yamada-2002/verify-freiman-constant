#!/usr/bin/env python3
"""Find point obstructions to affine bands, then replay them exactly in G."""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from exact import F,state_of
from audit_whole_scalar_intervals import sampled_gaps,witnesses
from scalar_obstructions import discover,replay
from verify_scalar_graph import verifier_for,ScalarVerifier


def replay_band(record):
    original=record['band_type']; cert=record['constant_certificate']
    data=dict(schema='kf131-sloped-atlas-v1',settings=record['settings'],nodes=[original])
    band=verifier_for(data)
    constant=ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',settings=cert['settings'],nodes=[cert['type']]))
    if (band.box(0)!=constant.box(0) or original['states']!=cert['type']['states']
            or original['parity']!=cert['type']['parity']):
        raise ValueError('obstruction geometry mismatch')
    params=list(map(F,cert['parameters'])); target=F(cert['target'])-F(original['scalar_slope'])*params[2]
    lo,hi=band.interval(original['interval'])
    if not lo<=target<=hi or target!=F(record['band_target']):
        raise ValueError('obstruction misses affine band')
    return replay(cert)


def audit(data,depth=7,budget=2000):
    v=verifier_for(data); found=[]; unresolved=[]
    for j,n in enumerate(data['nodes']):
        if n['covered']: continue
        span=v.interval(n['interval']); slope=F(n['scalar_slope']); obstruction=None
        for params in witnesses(v.box(j),True):
            shift=slope*params[2]; gspan=span[0]+shift,span[1]+shift
            for a,b in sampled_gaps(n,params,gspan,depth)[:16]:
                target=F(str((a+b)/2)); t=target-shift
                if not span[0]<=t<=span[1]: continue
                tree=discover(tuple(map(state_of,n['states'])),n['parity'],params,target,budget)
                if tree is None: continue
                # The constant certificate is only a vehicle for replaying
                # exclusion of this G point. Band membership is checked above.
                node=copy.deepcopy(n); node.pop('scalar_slope')
                node['interval']=[target.numerator-1,target.numerator+1]
                settings=dict(data['settings'],grid=target.denominator)
                cert=dict(type=node,settings=settings,parameters=list(map(str,params)),target=str(target),tree=tree)
                obstruction=dict(node=j,band_type=n,settings=data['settings'],band_target=str(t),constant_certificate=cert)
                obstruction['verification']=replay_band(obstruction); found.append(obstruction); break
            if obstruction: break
        if not obstruction: unresolved.append(j)
    return dict(obstructions=found,unresolved=unresolved,depth=depth,budget=budget,
                closed=False,scope='sampled point exclusions; absence of a witness is not a filling proof')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path); ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); raw=args.source.read_bytes(); result=audit(json.loads(raw))
    result.update(source=str(args.source),source_sha256=hashlib.sha256(raw).hexdigest())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(excluded=len(result['obstructions']),unresolved=result['unresolved'])))


if __name__=='__main__': main()
