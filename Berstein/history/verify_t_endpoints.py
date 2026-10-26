"""Cross-check uniform T input endpoints against the separate language DFA."""
import json
from pathlib import Path
from generalized_t import Language
from prepare_t import ends,cf

def main():
    base=Path(__file__).resolve().parents[1]
    meta=json.loads((base/'data'/'t_fine.meta.json').read_text())
    languages=[Language(((4,),(1,3,1))),Language(((3,),(4,),(1,3,1)))]
    checks=empty=0
    for aa in meta['prototypes']:
        a=tuple(aa)
        for uu in meta['extensions']:
            u=tuple(uu)
            for k,L in enumerate(languages):
                points=ends(a,u,k)
                direct=L.endpoint(a+u,True,48)
                assert (points is None)==(direct is None)
                if points is None:empty+=1;continue
                for i,minimum in enumerate((True,False)):
                    lo,hi=L.endpoint(a+u,minimum,48)
                    value=cf(a,points[i]);assert lo<=value<=hi
                    checks+=1
    out=dict(independent_endpoint_checks=checks,empty_language_checks=empty,passed=True)
    (base/'data'/'t_endpoints_verified.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))

if __name__=='__main__':main()
