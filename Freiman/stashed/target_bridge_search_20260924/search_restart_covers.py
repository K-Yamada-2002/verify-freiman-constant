#!/usr/bin/env python3
"""Search exact good, unmarked, equal-parity descendants as restart interfaces.

Local goodness is verified. All-depth filling additionally uses the restart
lemma explained in the companion report; it is not an output of this search.
"""
from pathlib import Path
from itertools import product
from functools import lru_cache
import argparse,json,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'Freiman_Hall_ray_verification/verification/checks/global'))
import literal_covers as l

def need(ok,msg):
    if not ok:raise ArithmeticError(msg)

def suffixes(base,depth):
    return [w for n in range(depth+1) for z in product('123',repeat=n)
            if '31313' not in base+(w:=''.join(z)) and
            not (base+w).endswith(('313','3131'))]

def search(n,depth,custom_root=None,ray_steps=0,safe_mixed=False):
    root=('3211'+'313121'*n+'3','4322'+'313121'*n)
    if custom_root is not None:root=tuple(custom_root)
    def candidates(base):
        if not ray_steps:return suffixes(base,depth)
        sys.path.insert(0,str(HERE.parent/'schecker_generalized'))
        import explore as e
        _,pre,period=e.extreme_tail(e.state_of(base),len(base)%2==0)
        ray=(pre+period*(ray_steps//len(period)+2))[:ray_steps]
        return sorted({ray[:i]+w for i in range(ray_steps+1)
                       for w in suffixes(base+ray[:i],depth)})
    left=candidates(root[0]);right=candidates(root[1])
    good=[];tested=0
    for u,v in product(left,right):
        pair=(root[0]+u,root[1]+v)
        if len(pair[0])%2!=len(pair[1])%2:
            if not safe_mixed or pair[l.wider(pair)].endswith('31'):continue
        if not (u or v):continue
        tested+=1
        lo,hi=l.interval(pair)
        if lo>=hi:continue
        g=l.goodness(pair)
        if g<=0:continue
        good.append((lo,hi,u,v,g))
    good.sort(key=lambda row:row[0])
    components=[]
    for row in good:
        lo,hi,*_=row
        if not components or components[-1]['upper']<lo:
            components.append(dict(lower=lo,upper=hi,rows=[row]))
        else:
            c=components[-1];c['rows'].append(row)
            if hi>c['upper']:c['upper']=hi
    out=[]
    for c in components:
        pos=c['lower'];chain=[]
        # Greedy minimum-cardinality interval cover, with exact comparisons.
        while pos<c['upper']:
            choices=[r for r in c['rows'] if r[0]<=pos and pos<r[1]]
            need(bool(choices),'component continuation')
            best=max(choices,key=lambda r:r[1]);chain.append(best);pos=best[1]
        out.append(dict(lower=c['lower'].json(),upper=c['upper'].json(),
            chain=[dict(suffixes=[r[2],r[3]],lower=r[0].json(),upper=r[1].json(),goodness=r[4].json()) for r in chain]))
    return dict(status='EXACT_LOCAL_RESTART_COVERS',family='custom' if custom_root else 'A',ray_steps=ray_steps,safe_mixed=safe_mixed,n=n,depth_per_side=depth,root=root,
                tested=tested,good_candidates=len(good),components=out,
                scope='Exact local cover and goodness; root coverage and all-index return still separate')

def verify(data):
    root=tuple(data['root'])
    if data.get('family','A')=='A':
        need(root==('3211'+'313121'*data['n']+'3','4322'+'313121'*data['n']),'root identity')
    else:need(root[0].startswith('32113') and root[1].startswith('4322'),'central root retained')
    def K(row):return l.K(row['a'],row['b'],row['radicand'])
    last=None
    for c in data['components']:
        lower,upper=K(c['lower']),K(c['upper']);pos=lower
        need(lower<upper,'component nonempty')
        if last is not None:need(last<lower,'separate components')
        for row in c['chain']:
            pair=tuple(a+b for a,b in zip(root,row['suffixes']))
            need(all(set(s)<=set('123') for s in row['suffixes']),'extension digits')
            need(all('31313' not in w and not w.endswith(('313','3131')) for w in pair),'unmarked admissible')
            need(len(pair[0])%2==len(pair[1])%2 or (data.get('safe_mixed',False) and not pair[l.wider(pair)].endswith('31')),'restart parity/first-step guard')
            lo,hi=l.interval(pair);g=l.goodness(pair)
            need(l.K()<g and (lo,hi,g)==tuple(K(row[k]) for k in ('lower','upper','goodness')),'exact row')
            need(lo<=pos<hi,'chain contact and advance');pos=hi
        need(pos==upper,'complete component');last=upper
    return True

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=0);ap.add_argument('--depth',type=int,default=3)
    ap.add_argument('--root',nargs=2);ap.add_argument('--ray-steps',type=int,default=0);ap.add_argument('--safe-mixed',action='store_true');ap.add_argument('--output',type=Path);ap.add_argument('--verify',type=Path);a=ap.parse_args()
    if a.verify:
        data=json.loads(a.verify.read_text());verify(data);print('PASS exact restart cover replay');raise SystemExit
    start=time.monotonic();data=search(a.n,a.depth,a.root,a.ray_steps,a.safe_mixed);verify(data);data['seconds']=time.monotonic()-start
    if a.output:a.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='components'},indent=2))
    print('components',len(data['components']),'chain lengths',[len(c['chain']) for c in data['components']],flush=True)
