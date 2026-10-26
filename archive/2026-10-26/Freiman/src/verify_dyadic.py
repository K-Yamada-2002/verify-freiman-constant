"""Independent Fraction replay of integer interval arithmetic and closure controls."""
from layout import SRC, BIN
import json,subprocess
from pathlib import Path
from layout import DATA
from fractions import Fraction as Q

BASE=DATA;D=1<<48

def main():
    subprocess.run(['clang++','-O3','-std=c++17',str(SRC/'check_dyadic.cpp'),'-o',str(BIN/'check_dyadic')],check=True)
    raw=subprocess.check_output([str(BIN/'check_dyadic')],text=True);count=0
    for line in raw.splitlines():
        a,b,c,d,pl,ph,ql,qh=map(int,line.split())
        products=[Q(x*y,D) for x in (a,b) for y in (c,d)]
        quotients=[Q(x*D,y) for x in (a,b) for y in (c,d)]
        assert pl<=min(products)<=max(products)<=ph
        assert ql<=min(quotients)<=max(quotients)<=qh
        assert min(products)-pl<1 and ph-max(products)<1
        assert min(quotients)-ql<1 and qh-max(quotients)<1
        count+=1
    controls=[]
    # Affine Cantor contractions x -> 3*x/8 and x -> 5/8+3*x/8.
    # Their sums have a strict overlap for scale ratios in [7/8,9/8].
    for good in (True,False):
        pairs=[(1,1),(1,2),(2,1),(2,2)] if good else [(1,1)]
        lines=[f'FREIMAN_DYADIC_V1 1 3 0 0 1 {len(pairs)} 0',f'0 {D}']
        lines.extend(f'{u} {w} 0' for u,w in pairs)
        lines.extend((f'{7*D//8} {7*D//8}',f'{9*D//8} {9*D//8}',f'{D} {D}'))
        def bounds(q):return q.numerator//q.denominator,-((-q.numerator)//q.denominator)
        for lo,hi,gamma in ((Q(0),Q(1),Q(1)),(Q(0),Q(3,8),Q(3,8)),(Q(5,8),Q(1),Q(3,8))):
            gl,gh=bounds(gamma*D);ll,lh=bounds(lo*D);hl,hh=bounds(hi*D)
            lines.append(f'0 0 {1 if gamma==1 else 2} {gl} {gh} {ll} {lh} {hl} {hh}')
        name='invariant_control_'+('cover' if good else 'gap')
        (BASE/(name+'.dat')).write_text('\n'.join(lines)+'\n')
        subprocess.run([str(BIN/'invariant_kernel'),str(BASE/(name+'.dat')),str(BASE/(name+'.json'))],check=True,capture_output=True)
        result=json.loads((BASE/(name+'.json')).read_text())
        assert result['closed_family_found']==good
        controls.append({'case':name,'closed_family_found':result['closed_family_found']})
    result={'passed':True,'rational_arithmetic_cases':count,'closure_controls':controls}
    (BASE/'dyadic_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
