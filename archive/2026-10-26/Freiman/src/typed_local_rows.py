"""Three small, universal Schecker-style rows. Closure is a separate problem."""
import json
from fractions import Fraction as Q
from pathlib import Path
from layout import DATA
from typed_boxes import Uniform
from box_certificates import encode_box
from exact_cf import parameters


def rows():
    forward=[((3,),(2,),'T2'),((2,),(),'T2'),((1,),(),'T2')]
    reverse=[((1,),(),'T2'),((),(2,),'T2'),((2,),(3,),'T2')]
    specifications=[
        ('321133','432212',((Q(3,10),Q(4,13)),(Q(1,3),Q(2,5)),(Q(5,12),Q(3,5))),forward),
        ('3211311','43221',((Q(1,2),Q(2,3)),(Q(2,3),Q(3,4)),(Q(3,2),Q(2))),reverse),
        ('321132','432211',((Q(3,7),Q(4,9)),(Q(1,2),Q(2,3)),(Q(1,2),Q(3,4))),forward),
    ]
    result=[]
    for aa,bb,box,menu in specifications:
        a,b=tuple(map(int,aa)),tuple(map(int,bb))
        assert all(lo<=x<=hi for x,(lo,hi) in zip(parameters(a,b),box))
        proof=Uniform(a,b,'T2',box);assert proof.verify(menu)
        result.append({'a':aa,'b':bb,'type':'T2','box':encode_box(box),'menu':menu,
                       'uniform_comparisons':proof.checks})
    return result


if __name__=='__main__':
    result={'proof_complete':False,'local_rows_proved':True,'coordinate':'denominator_ratio_squared',
            'scope':'Uniform local covers only; child admissibility is not proved.','rows':rows()}
    (DATA/'typed_local_rows.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
