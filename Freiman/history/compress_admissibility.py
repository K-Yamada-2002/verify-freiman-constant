"""Lossless compression of the saved admissibility tables, not a new proof.

Combine consecutive S bins with the same type, combine consecutive type
indices with the same bin range, and use (a,b,S) <-> (b,a,1/S).
Reconstruct and compare EVERY original byte before writing the result.
The compressed predicates need not have a single uniform successor menu.
"""
import hashlib
import json
from collections import defaultdict
from layout import DATA


def runs(raw, geometry, bins, types, stop):
    result = defaultdict(list)
    count = 0
    for typ in range(types):
        start = None
        for k in range(stop + 1):
            live = k < stop and raw[(geometry*bins+k)*types+typ]
            if live and start is None:
                start = k
            if not live and start is not None:
                result[start, k-1].append(typ)
                count += 1
                start = None
    return result, count


def compress(name):
    meta_path = DATA / (name + '.meta.json')
    bits_path = DATA / (name + '.json.alive.bin')
    meta = json.loads(meta_path.read_text())
    raw = bits_path.read_bytes()
    sides, types = len(meta['side_keys']), len(meta['types'])
    low, high = meta['low'], meta['high']
    bins = high-low+1
    assert low == -high-1 and bins % 2 == 0
    assert len(raw) == sides*sides*bins*types and all(x in (0, 1) for x in raw)
    original_runs = 0
    rows = []
    for a in range(sides):
        for b in range(sides):
            geometry = a*sides+b
            _, count = runs(raw, geometry, bins, types, bins)
            original_runs += count
            if a > b:
                continue
            # On the diagonal, the positive half is the mirror of the negative.
            stop = bins//2 if a == b else bins
            groups, _ = runs(raw, geometry, bins, types, stop)
            for (first, last), selected in sorted(groups.items()):
                begin = end = selected[0]
                for typ in selected[1:] + [types+1]:
                    if typ == end+1:
                        end = typ
                    else:
                        rows.append([a, b, first+low, last+low, begin, end])
                        begin = end = typ
    restored = bytearray(len(raw))
    for a, b, first, last, begin, end in rows:
        for i in range(first, last+1):
            for typ in range(begin, end+1):
                restored[((a*sides+b)*bins+i-low)*types+typ] = 1
                restored[((b*sides+a)*bins+(-i-1)-low)*types+typ] = 1
    assert bytes(restored) == raw, 'Compression did not exactly reproduce the saved family'
    result = {
        'kernel': name,
        'scope': 'Lossless admissibility predicates only; no new uniform menus or smaller proof established.',
        'row_fields': ['left_side_id', 'right_side_id', 'first_bin', 'last_bin', 'first_type', 'last_type'],
        'interpretation': 'Each row includes all indicated types and closed S interval [base**first_bin, base**(last_bin+1)], plus its left/right swapped reciprocal image.',
        'side_keys': meta['side_keys'], 'bands': meta['bands'], 'base': meta['base'],
        'prehistory_interval': meta.get('prehistory_interval', ['0','1']),
        'original_universe_size': len(raw), 'original_adopted_rows': sum(raw),
        'conditions_after_merging_ratio_bins': original_runs,
        'compressed_conditions': len(rows), 'exact_byte_reconstruction': True,
        'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (meta_path,bits_path)},
        'rows': rows,
    }
    (DATA / (name + '_compressed_admissibility.json')).write_text(json.dumps(result,indent=2)+'\n')
    return {k:v for k,v in result.items() if k in (
        'kernel','original_universe_size','original_adopted_rows',
        'conditions_after_merging_ratio_bins','compressed_conditions','exact_byte_reconstruction')}


if __name__ == '__main__':
    results = [compress(name) for name in ('graph_m2','graph_wide')]
    (DATA / 'admissibility_compression_summary.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
