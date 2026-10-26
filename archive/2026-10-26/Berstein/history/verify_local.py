"""Replay the saved local T cover, then certify why its second child fails."""
import json
from fractions import Fraction as Q
from pathlib import Path
from generalized_t import Language
from search_t import interval, ge, outer_gaps
from exact_cf import interval as full_interval
from itertools import product

def main():
    base=Path(__file__).resolve().parents[1]
    binary=Language(((4,),(1,3,1),(3,)))
    full=Language(((4,),(1,3,1)))
    U,V=(1,1,2),(1,2,2)
    menu=[((1,),()),((2,),()),((3,),(2,))]
    parent=interval(U,V,binary,full)
    children=[interval(U+u,V+v,binary,full) for u,v in menu]
    assert ge(parent[0],children[0][0]) and ge(children[-1][1],parent[1])
    assert all(ge(a[1],b[0]) and ge(b[1],a[0]) for a,b in zip(children,children[1:]))
    H=(Q('1.295458'),Q('1.295459'))
    child=children[1]
    assert child[0].bounds(48)[1]<H[0]<H[1]<child[1].bounds(48)[0]
    gaps=outer_gaps(U+(2,),V,3)
    witness=next((a,b) for a,b in gaps if a<H[0]<H[1]<b)
    assert children[0][1].bounds(48)[1]<H[0]
    assert H[1]<children[2][0].bounds(48)[0]
    first=[(i,j,full_interval(U+(i,),V+(j,))) for i,j in product((1,2,3),repeat=2)]
    # Every first-digit rectangle meeting H has left digit 2; the certified
    # gap of K_F(U2)+K_F(V) therefore excludes H from the entire root sum too.
    assert all(i==2 or hi<H[0] or H[1]<lo for i,j,(lo,hi) in first)
    report=dict(local_cover_proved=True,closed_recursion=False,
        root=['112','122'],B1=['4','131','3'],B2=['4','131'],
        menu=[['1',''],['2',''],['3','2']],
        failed_child=['1122','122'],rational_gap=[str(x) for x in H],
        exact_outer_gap=[x.data() for x in witness],
        reason='H is a genuine gap of both the second child and the entire root cylinder sum.',
        root_cylinder_sum_excluded=True,
        global_sum_excluded=False,interior_proved=False)
    (base/'data'/'local_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__':main()
