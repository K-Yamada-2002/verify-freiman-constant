"""Prepare coarse-S search inputs; this does not establish a certificate."""
import argparse
import json
from fractions import Fraction
from certified_kernel_input import enclosing
from endpoint_return import S0
from layout import DATA


def prepare(stride):
    assert stride >= 2
    source = 'graph_wide'
    meta = json.loads((DATA / (source + '.meta.json')).read_text())
    lines = (DATA / (source + '.dat')).read_text().splitlines()
    magic, *header = lines[0].split()
    sides, extensions, low, high, types, pairs, root = map(int, header)
    assert magic == 'FREIMAN_DYADIC_GRAPH_V1'
    assert (low, high) == (meta['low'], meta['high'])
    geometry = root // (high-low+1)
    side_data = lines[1+types+pairs+(high-low+2):]
    base = Fraction(meta['base']) ** stride
    new_low = -(max(-low, high+1)//stride+1)
    new_high = -new_low-1
    bins = new_high-new_low+1
    root_bin = next(i for i in range(new_low, new_high+1)
                    if base**i <= S0 <= base**(i+1))
    new_root = geometry*bins+root_bin-new_low
    meta.update(base=str(base), low=new_low, high=new_high,
                root_geometry_id=new_root, source_numerical_universe=source,
                coarsening_stride=stride)
    name = f'coarse_s{stride}'
    (DATA / (name + '.meta.json')).write_text(json.dumps(meta, indent=2)+'\n')
    new = [f'{magic} {sides} {extensions} {new_low} {new_high} {types} {pairs} {new_root}']
    new += lines[1:1+types+pairs]
    new += [' '.join(map(str, enclosing(base**i)))
            for i in range(new_low, new_high+2)]
    new += side_data
    (DATA / (name + '.dat')).write_text('\n'.join(new)+'\n')
    print(json.dumps({'input': name, 'bins': bins, 'proposal_only': True}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('strides', nargs='*', type=int, default=[4, 8, 16])
    for stride in parser.parse_args().strides:
        prepare(stride)
