"""Explore actual asymmetric generalized T-intervals, keeping forbidden tests
on the entire outward prefix. These are discovery results, not filling claims.
"""
from functools import lru_cache
from itertools import product
from pathlib import Path
from layout import DATA
import json
from exact_cf import cf,periodic,CF,union

B0=((3,1,3,1,3),)
LANGUAGES={
    'base':B0,
    'no33':B0+((3,3),),
    'no22_no33':B0+((2,2),(3,3)),
    'no11':B0+((1,1),),
}


@lru_cache(None)
def states(kind):
    return tuple(sorted({w[:n] for w in LANGUAGES[kind] for n in range(len(w))}))


@lru_cache(None)
def step(kind,state,digit):
    word=state+(digit,)
    if any(word[-len(w):]==w for w in LANGUAGES[kind]):return None
    return max((s for s in states(kind) if not s or word[-len(s):]==s),key=len)


@lru_cache(None)
def scan(kind,word):
    state=()
    for digit in word:
        state=step(kind,state,digit)
        if state is None:return None
    return state


@lru_cache(None)
def tail(kind,state,minimize):
    seen={};digits=[];odd=True
    while (state,odd) not in seen:
        seen[state,odd]=len(digits)
        choices=[d for d in (1,2,3) if step(kind,state,d) is not None]
        # For these four languages every allowed state has an infinite
        # continuation: periodic 12 suffices even for the no11 language.
        d=max(choices) if minimize==odd else min(choices)
        digits.append(d);state=step(kind,state,d);odd=not odd
    n=seen[state,odd]
    return cf(tuple(digits[:n]),periodic(tuple(digits[n:])))


@lru_cache(None)
def side(kind,word):
    state=scan(kind,word)
    if state is None:return None
    return tuple(cf(word,tail(kind,state,minimize==(len(word)%2==0))) for minimize in (True,False))


@lru_cache(None)
def hull(k1,k2,a,b):
    intervals=[]
    for l,r in ((k1,k2),(k2,k1)):
        aa,bb=side(l,a),side(r,b)
        if aa is not None and bb is not None:
            intervals.append((aa[0]+bb[0],aa[1]+bb[1]))
    return (min(x[0] for x in intervals),max(x[1] for x in intervals)) if intervals else None


def audit(k1,k2,a,b,depth):
    words=list(product((1,2,3),repeat=depth));intervals=[]
    for u in words:
        for w in words:
            iv=hull(k1,k2,a+u,b+w)
            if iv:intervals.append(iv)
    merged=union(intervals)
    return [(x[1],y[0]) for x,y in zip(merged,merged[1:])]


if __name__=='__main__':
    a,b=tuple(map(int,'32113')),tuple(map(int,'4322'));rows=[]
    for k1 in LANGUAGES:
        k2='base';iv=hull(k1,k2,a,b)
        if iv is None:continue
        row={'languages':[k1,k2],'root':['32113','4322'],
             'hull':[x.data() for x in iv],'centered_hull_decimal':[float(4+x) for x in iv],
             'lower_endpoint_exact_cF':iv[0]+4==CF,'audits':[]}
        for d in (1,2,3):
            gaps=audit(k1,k2,a,b,d)
            row['audits'].append({'depth':d,'exact_gap_count':len(gaps),
                                 'first_gap':[x.data() for x in gaps[0]] if gaps else None})
        rows.append(row);print(json.dumps(row),flush=True)
    (DATA/'language_variants.json').write_text(json.dumps({'proof_complete':False,'records':rows},indent=2)+'\n')
