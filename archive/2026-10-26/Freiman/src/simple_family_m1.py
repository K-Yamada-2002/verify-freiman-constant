"""Experimental common family after forgetting the penultimate digit.

The output is a proposal, not a proof. Closure must be checked separately.
"""
import argparse
import json
from collections import defaultdict
from layout import DATA


def propose(source='graph_wide', name='simple_family_m1'):
    meta = json.loads((DATA / (source + '.meta.json')).read_text())
    raw = (DATA / (source + '.json.alive.bin')).read_bytes()
    sides = meta['side_keys']
    S, B, T = len(sides), meta['high'] - meta['low'] + 1, len(meta['types'])
    groups = defaultdict(list)
    for a, ka in enumerate(sides):
        ga = (ka[0], ka[1], ka[2][-1])
        for b, kb in enumerate(sides):
            gb = (kb[0], kb[1], kb[2][-1])
            groups[(ga, gb)].append(a*S+b)
    out = bytearray(len(raw))
    represented = 0
    runs = 0
    lower = 0
    for (ga, gb), geoms in groups.items():
        common = bytearray([1]) * (B*T)
        for g in geoms:
            off = g*B*T
            for j in range(B*T):
                common[j] &= raw[off+j]
        for g in geoms:
            out[g*B*T:(g+1)*B*T] = common
        represented += sum(common)
        if ga <= gb:
            stop = B//2 if ga == gb else B
            local_runs=[]
            for t in range(T):
                prev=0; n=0
                for k in range(stop):
                    value=common[k*T+t]
                    n += bool(value and not prev)
                    prev=value
                local_runs.append(n)
            runs += sum(local_runs)
            lower += max(local_runs)
    assert all(not b or a for a,b in zip(raw,out))
    (DATA/(name+'.seed.bin')).write_bytes(out)
    group_ids = {}
    for group_id, members in enumerate(groups.values()):
        for geometry in members:
            group_ids[geometry] = group_id
    (DATA/(name+'.groups.txt')).write_text(
        str(len(groups))+'\n'
        +' '.join(str(group_ids[g]) for g in range(S*S))+'\n')
    (DATA/(name+'.dat')).write_bytes((DATA/(source+'.dat')).read_bytes())
    (DATA/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n')
    result={'proposal_only':True,'source':source,'coarse_geometry_pairs':len(groups),
            'coarse_rows':represented,'fine_rows':sum(out),
            'individual_type_runs_after_swap':runs,
            'rectangle_lower_bound_after_swap':lower}
    (DATA/(name+'_proposal.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', default='graph_wide')
    parser.add_argument('--name', default='simple_family_m1')
    args = parser.parse_args()
    propose(args.source, args.name)
