#!/usr/bin/env python3
"""Merge two adjacent products only after checking all new cross pairs."""
import argparse,json
from pathlib import Path
from fractions import Fraction as Q
from search import merge
from reduce_cover import antichain,dominance,background
from target_cover import ThresholdModel,complement
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,default=ROOT/'rebuilt_cover.json');p.add_argument('--output',type=Path,default=ROOT/'replacement_cover.json');args=p.parse_args()
    data=json.loads(args.input.read_text());rows=data['claims'];assert len(rows)==11
    assert all(c['scan']['complete'] and c['scan']['covers_target'] for c in rows)
    a,b=rows[8:10];assert a['graph']==b['graph']
    spec=a['model'];m=ThresholdModel(spec['digits'],spec['radius'],spec['threshold'])
    left,right=antichain(a['left']+b['left']),antichain(a['right']+b['right'])
    bound=max(background(m),dominance(m,left,right));lo=Q(str(a['target'][0]));hi=Q(str(b['target'][1]));assert bound<lo
    for c in (a,b):
        assert all(any(w.startswith(p) for p in left) for w in c['left'])
        assert all(any(w.startswith(p) for p in right) for w in c['right'])
    intervals=merge([tuple(map(Q,z)) for c in (a,b) for z in c['rational_leaf_check']['covered']])
    assert not complement(intervals,lo,hi)
    width=max(Q(c['rational_leaf_check']['maximum_width']) for c in (a,b))
    combined=dict(left=left,right=right,model=spec,graph=a['graph'],target=[float(lo),float(hi)],dominance_bound=str(bound),
                  origin='old 8 and repaired old 9; full Cartesian product',
                  rational_leaf_check=dict(covered=[[str(x),str(y)] for x,y in intervals],maximum_width=str(width)),
                  scan=dict(complete=True,covers_target=True,exponent=data['exponent'],
                            evidence='Union of certified subproduct covers; every leaf belongs to this full product. New cross pairs independently dominance-checked.'),
                  source_rows=[9,10])
    data['claims']=rows[:8]+[combined]+rows[10:];data['source']=str(args.input)
    data['merge_audit_replacement']={'source_rows':[9,10],'new_dominance_bound':str(bound),'margin':str(lo-bound)}
    assert not complement([tuple(Q(str(x)) for x in c['target']) for c in data['claims']],Q('4.1'),Q('4.52'))
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print('10 propositions; exact target coverage and all cross-pair dominance checked')
if __name__=='__main__':main()
