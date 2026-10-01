"""A lower bound for lossless, fixed-geometry rectangular descriptions.

One condition fixes both side IDs, restricts S to one interval and restricts
types independently of S. Its swapped reciprocal image is included for free.
This does NOT bound other admissible families or conditions coupling S/type.
"""
import hashlib
import json
from layout import DATA


def bound(name):
    metadata = DATA / (name + '.meta.json')
    certificate = DATA / (name + '.json.alive.bin')
    meta = json.loads(metadata.read_text())
    raw = certificate.read_bytes()
    sides, types = len(meta['side_keys']), len(meta['types'])
    low, high = meta['low'], meta['high']
    bins = high - low + 1
    assert low == -high - 1 and bins % 2 == 0
    assert len(raw) == sides * sides * bins * types
    witnesses = []
    for a in range(sides):
        for b in range(a, sides):
            for k in range(bins):
                left = ((a*sides+b)*bins+k)*types
                right = ((b*sides+a)*bins+bins-1-k)*types
                assert raw[left:left+types] == raw[right:right+types]
            stop = bins//2 if a == b else bins
            best_runs, best_type = [], None
            for typ in range(types):
                runs, start = [], None
                for k in range(stop + 1):
                    live = k < stop and raw[((a*sides+b)*bins+k)*types+typ]
                    if live and start is None:
                        start = k
                    if not live and start is not None:
                        runs.append([start+low, k-1+low])
                        start = None
                if len(runs) > len(best_runs):
                    best_runs, best_type = runs, typ
            witnesses.append({'left': a, 'right': b, 'type': best_type,
                              'separated_runs': best_runs})
    return {
        'kernel': name,
        'scope': 'Exact saved table; each condition fixes a side-ID pair and has one S interval, with reciprocal symmetry free. Type selection is independent of S.',
        'not_a_bound_for_new_families_or_other_predicate_languages': True,
        'lower_bound': sum(len(w['separated_runs']) for w in witnesses),
        'proof': 'At a fixed type one rectangular condition meets at most one separated live run. Take the maximum run count over types for each canonical geometry, then sum over geometries.',
        'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in (metadata, certificate)},
        'witnesses': witnesses,
    }


if __name__ == '__main__':
    results = [bound(name) for name in ('graph_m2', 'graph_wide')]
    (DATA / 'admissibility_rectangle_bound.json').write_text(
        json.dumps(results, indent=2) + '\n')
    print(json.dumps([{k: r[k] for k in ('kernel', 'lower_bound')}
                      for r in results], indent=2))
