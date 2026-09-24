#!/usr/bin/env python3
"""Clip the rejected second row, add its replacement, and merge safe products."""
from fractions import Fraction as Q
import json
from pathlib import Path
from search import merge
from target_cover import ThresholdModel,complement
from reduce_cover import antichain,dominance,background
ROOT=Path(__file__).resolve().parent

def main():
    data=json.loads((ROOT/'rebuilt_cover.json').read_text());rows=data['claims'];assert len(rows)==11
    assert all(c['scan']['complete'] for c in rows)
    assert all(c['scan']['covers_target'] for i,c in enumerate(rows) if i!=1)
    c=rows[1];c['target']=[4.124768,4.1615813]
    lo,hi=map(lambda x:Q(str(x)),c['target'])
    clipped=[(max(lo,Q(a)),min(hi,Q(b))) for a,b in c['rational_leaf_check']['covered'] if Q(a)<=hi and Q(b)>=lo]
    assert not complement(clipped,lo,hi)
    c['rational_leaf_check']['covered']=[[str(a),str(b)] for a,b in clipped]
    c['scan']={'complete':True,'covers_target':True,'exponent':9,'evidence':'Exact clipping of the complete scan in rebuilt_cover.json row 2; the rejected gap lies outside the shortened target.'}
    repair=json.loads((ROOT/'research_second_split.json').read_text())['claims'][0]
    s={k:repair['proposition'][k] for k in ('left','right','target','graph','model','dominance_bound')};scan=repair['scan']
    assert scan['complete'] and scan['covers_target'] and scan['exponent']==9
    s['scan']=scan;s['origin']='second repair of old row 1'
    s['rational_leaf_check']={'covered':[[str(Q(a,scan['scale'])+3),str(Q(b,scan['scale'])+3)] for a,b in scan['covered']], 'maximum_width':str(Q(scan['max_width_units'],scan['scale']))}
    a,b=rows[8:10];assert a['graph']==b['graph'];spec=a['model'];m=ThresholdModel(spec['digits'],spec['radius'],spec['threshold'])
    left,right=antichain(a['left']+b['left']),antichain(a['right']+b['right'])
    bound=max(background(m),dominance(m,left,right));start,end=Q(str(a['target'][0])),Q(str(b['target'][1]));assert bound<start
    for orig in (a,b):
        assert all(any(w.startswith(p) for p in left) for w in orig['left'])
        assert all(any(w.startswith(p) for p in right) for w in orig['right'])
    intervals=merge([tuple(map(Q,z)) for orig in (a,b) for z in orig['rational_leaf_check']['covered']]);assert not complement(intervals,start,end)
    combined=dict(left=left,right=right,model=spec,graph=a['graph'],target=[float(start),float(end)],dominance_bound=str(bound),
                  rational_leaf_check=dict(covered=[[str(x),str(y)] for x,y in intervals],maximum_width=str(max(Q(orig['rational_leaf_check']['maximum_width']) for orig in (a,b)))),
                  scan=dict(complete=True,covers_target=True,exponent=9,evidence='Union of two certified subproduct covers; all new cross pairs dominance-checked.'),source_rows=[9,10])
    data['claims']=rows[:2]+[s]+rows[2:8]+[combined]+rows[10:]
    data['definitions'].append(repair['definition']);data['source']='rebuilt_cover.json + research_second_split.json'
    data['transformations']=['Shortened raw row 2 to end at 4.1615813 before its rigorously detected gap.', 'Inserted a new safe product covering [4.161580,4.171799].', 'Merged raw rows 9 and 10; checked every cross pair.']
    all_intervals=[tuple(Q(str(x)) for x in c['target']) for c in data['claims']]
    assert not complement(all_intervals,Q('4.1'),Q('4.52'))
    for c in data['claims']:
        a,b=map(lambda x:Q(str(x)),c['target']);assert not complement([tuple(map(Q,z)) for z in c['rational_leaf_check']['covered']],a,b)
        assert Q(c['rational_leaf_check']['maximum_width'])<=Q(1,10**9)
        assert Q(c['dominance_bound'])+Q(1,10**9)<a
    (ROOT/'replacement_cover.json').write_text(json.dumps(data,indent=2)+'\n')
    print('Final 11 propositions: exact finite coverage at 1e-9, no gaps, positive dominance margins.')
if __name__=='__main__':main()
