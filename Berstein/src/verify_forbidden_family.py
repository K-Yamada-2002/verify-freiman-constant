"""Exhaust the short extra-forbidden-word choices at the fixed root 112,122."""
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from generalized_t import Language
from search_t import interval,obstructed

def main():
    base=((4,),(1,3,1));F=Language(base);U,V=(1,1,2),(1,2,2)
    H=(Q('1.295458'),Q('1.295459'))
    def has_gap(iv):return iv[0].bounds(48)[1]<H[0]<H[1]<iv[1].bounds(48)[0]
    words=[w for n in (1,2,3) for w in product((1,2,3),repeat=n)]
    single=[]
    for w in words:
        iv=interval(U,V,Language(base+(w,)),F)
        assert iv is None or has_gap(iv)
        single.append(dict(extra=''.join(map(str,w)),empty=iv is None,contains_proved_gap=iv is not None))
    languages=[('F',F)]+[(''.join(map(str,w)),Language(base+(w,))) for w in words if w!=(1,3,1)]
    empty=blocked=0;exceptions=[]
    for i,(left,A) in enumerate(languages):
        for right,B in languages[i:]:
            iv=interval(U,V,A,B)
            if iv is None:empty+=1
            elif has_gap(iv):blocked+=1
            else:exceptions.append(dict(left=left,right=right,another_gap_at_depth4=obstructed(U,V,iv,4)))
    assert empty==120 and blocked==657 and len(exceptions)==3
    report=dict(root=['112','122'],proved_gap=[str(x) for x in H],
                single_extra=single,pairs_examined=780,empty_pairs=empty,
                pairs_containing_proved_gap=blocked,exceptions=exceptions,
                scope='Obstructions for these fixed root/type choices, not nonexistence of interior.',interior_proved=False)
    out=Path(__file__).resolve().parents[1]/'data'/'forbidden_family_verified.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(single_choices=len(single),single_nonempty=sum(not x['empty'] for x in single),
                         pair_choices=780,empty=empty,blocked=blocked,exceptions=exceptions)))

if __name__=='__main__':main()
