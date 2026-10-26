"""Small independent, exact checks: real gaps and global-language semantics."""
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from exact_cf import K, interval, side_endpoint, tail_endpoint, cf
from language import scan, STATES
from generalized_t import Language, generalized_t


def main():
    base=Path(__file__).resolve().parents[1]
    full=Language(((1,3,1),),(1,2,3))
    # Independent DFA/extremal implementation and rational bracketing.
    count=0
    for n in range(5):
        for w in product((1,2,3),repeat=n):
            assert (full.scan(w) is None)==(scan(w) is None)
            if scan(w) is None:continue
            for minimize in (True,False):
                lo,hi=full.endpoint(w,minimize,48)
                assert lo<=side_endpoint(w,minimize)<=hi
                count+=1
    U=(1,3)
    parent=interval(U,U)
    children=[(u,v,interval(U+(u,),U+(v,))) for u,v in product((2,3),repeat=2)]
    H=(Q('1.5358'),Q('1.5360'))
    assert parent[0]<H[0]<H[1]<parent[1]
    assert all(hi<H[0] or H[1]<lo for _,_,(lo,hi) in children)
    # A gap for (13,13) is not an exclusion from the global K_F+K_F.
    assert scan(U+(1,)) is None
    # Uniform obstruction, independent of prefix length or sampled shapes.
    a,b=sorted(cf((3,),tail_endpoint(scan(U+(3,)),t)) for t in (True,False))
    c,d=sorted(cf((2,),tail_endpoint(scan(U+(2,)),t)) for t in (True,False))
    assert a<b<c<d
    # gap/width = (c-b)/(b-a) * (1+r*a)/(1+r*c), decreasing on [0,1].
    threshold=(c-b)/(b-a)*(1+a)/(1+c)
    assert threshold>Q(6,5)
    binary=Language(((3,),(4,)))
    ternary=Language(((4,),))
    assert generalized_t((3,),(3,),binary,ternary) is None
    assert generalized_t((3,),(2,),binary,ternary) is not None
    dead=Language(((1,1),(1,2)),(1,2))
    assert dead.scan((1,)) is None and dead.scan((2,)) is not None
    empty=Language(((1,),(2,)),(1,2))
    assert empty.hull(()) is None
    no13=Language(((1,3),),(1,2,3))
    short=(1,1,2,2,1);violated=(1,3,2,2,1)
    assert short[-3:]==violated[-3:] and scan(short)==scan(violated)
    assert no13.scan(short) is not None and no13.scan(violated) is None
    result=dict(status='proved',independent_endpoint_checks=count,
                word_pair=['13','13'],gap=[str(t) for t in H],
                parent=[[str(x.a),str(x.b)] for x in parent],
                children=[dict(digits=[u,v],endpoints=[x.data() for x in iv]) for u,v,iv in children],
                claim='H is inside the full hull but disjoint from K_F(13)+K_F(13).',
                uniform_obstruction=dict(suffix='13',same_parity=True,
                    small_branch_width_ratio=['5/6','6/5'],
                    gap_width_threshold=threshold.data(),
                    threshold_strictly_greater_than='6/5'),
                global_sum_excluded=False,interior_proved=False)
    (base/'data'/'obstructions.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False))

if __name__=='__main__':main()
