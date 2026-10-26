"""Exact bulk bounds for the two experimental tail languages, not filling."""
import hashlib
import json
from itertools import product
from pathlib import Path
import prepare_313 as language_api
from prepare_313 import configure,scan,cf,tail_endpoint,E,side_interval,matrix,extremal_tail
from spectral_rational import RationalBounds


def main():
    results=[]
    for language in ['313','31313,13131']:
        configure(language)
        forbidden=[tuple(map(int,w)) for w in language.split(',')]
        n=max(map(len,forbidden));k=n//2
        def maximum(w,s):
            return cf(w,tail_endpoint(s,len(w)%2==1))
        values=[]
        for w in product((1,2,3),repeat=n):
            if scan(w) is None:continue
            # These odd windows are at least as long as every forbidden word.
            # No forbidden word can touch both remaining outside tails, so
            # their separate exact maxima give a uniform bilateral bound.
            value=w[k]+maximum(w[:k][::-1],scan(w[::-1]))+maximum(w[k+1:],scan(w))
            values.append((value,w))
        value,witness=max(values)
        expected=E.quad(0,2,5) if language=='313' else E.quad(0,'4/181',41667)
        assert value==expected
        rational=RationalBounds(forbidden,backward=8).far()[0]
        assert value<E.cast(rational)
        results.append(dict(language=language,radicand=E.basis[2],basis=E.basis,
                            bulk_upper=value.data(),decimal=float(value),
                            maximizing_window=witness,legal_windows=len(values),
                            rational_far_upper=str(rational)))
        if language=='31313,13131':
            multiplier=E.quad(1633,8,41667)
            return_factor=1/(multiplier*multiplier)
            returning_cases=0
            for state in language_api.STATES:
                for minimum in (True,False):
                    pre,per=extremal_tail(state,minimum)
                    u=(pre+per*11)[:10]
                    x=tail_endpoint(state,minimum)
                    y=tail_endpoint(scan(state+u),minimum)
                    assert cf(u,y)==x
                    A,B,C,D=matrix(u)
                    assert C*y+D==multiplier
                    assert 1/((C*y+D)*(C*y+D))==return_factor
                    returning_cases+=1
            results[-1]['period10_return']=dict(
                state_parity_cases=returning_cases,factor=return_factor.data(),
                factor_decimal=float(return_factor),same_factor_in_every_case=True)
            a,b=(3,1,1,3),(4,3,1,3)
            aa,bb=side_interval(a),side_interval(b)
            low,high=(4+aa[i]+bb[i] for i in (0,1))
            spectral=RationalBounds(forbidden,backward=8).root(a,b,4)
            assert E.cast(spectral['theta'])<low<high<E.cast('4.52')
            results[-1]['conditional_root']=dict(
                a='3113',b='4313',center=4,hull=[low.data(),high.data()],
                hull_decimal=[float(low),float(high)],spectral=spectral,
                interval_filling_proved=False,
                scope='All-position domination holds over the whole hull; no filling or interval inclusion is claimed.')
    root=Path(__file__).resolve().parents[2]
    files=[Path(__file__).resolve(),root/'Berstein/src/prepare_313.py',
           root/'Berstein/src/field.py',root/'Berstein/src/spectral_rational.py']
    report=dict(passed=True,scope='Uniform tail bounds only; no interval filling claim.',
                results=results,sha256={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files})
    (root/'Berstein/data/exploration_bulk_bounds.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='sha256'},indent=2))


if __name__=='__main__':main()
