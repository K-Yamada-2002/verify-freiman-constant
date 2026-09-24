#!/usr/bin/env python3
"""Necessary interval-length inequalities for a fixed return family.

For uniform sets S_i in the normalized scalar coordinate, at one exact
parameter point per shape/ratio type, any cover implies m_i <= sum A_ij m_j.
A positive rational v with A v < v excludes positive measure for this fixed
family, even if its scalar intervals are repositioned, shrunk, or split.
It does not exclude new parameter types, other words, or moving intervals.
"""
import argparse
import copy
import hashlib
import json
import math
from functools import lru_cache
from pathlib import Path

from exact import F
from anchored_geometry import B,factor
from close_scalar_library import geometry_moves
from graft_gap_repairs import geometry
from scalar_obstructions import rational_in
from verify_scalar_graph import ScalarVerifier


@lru_cache(maxsize=65536)
def point_gains(word,r):
    square=factor(word,r)**2
    return square,1/square


def margins(matrix,weights):
    if not all(x > 0 for x in weights):
        return None
    result=[]
    for i,row in enumerate(matrix):
        delta=B.coerce(weights[i])-sum((a*weights[j] for j,a in row.items()),B())
        if delta<=0:
            return None
        result.append(delta)
    return result


def expansion_witness(matrix):
    """Exact Av >= v witness; only shows this width test cannot exclude closure."""
    numeric=[{j:float(a.decimal()) for j,a in row.items()} for row in matrix]
    weights=[1.0]*len(matrix)
    for iteration in range(1,129):
        new=[sum(a*weights[j] for j,a in row.items()) for row in numeric]
        scale=max(new,default=0)
        if not scale or not math.isfinite(scale):
            return None
        weights=[x/scale for x in new]
        if iteration%16:
            continue
        rational=[F(round(x*10**8),10**8) for x in weights]
        delta=[sum((a*rational[j] for j,a in row.items()),B())-rational[i]
               for i,row in enumerate(matrix)]
        if any(rational) and all(x>=0 for x in delta):
            return dict(iteration=iteration,weights=list(map(str,rational)),
                        margins=[x.record() for x in delta],
                        meaning='Av >= v; excludes a strict positive contraction weight, not a cover proof')
    return None


def audit(data,length=4,return_blocks=True):
    unique = []
    keys = {}
    for n in data['nodes']:
        key = geometry(n)
        if key not in keys:
            keys[key] = len(unique)
            row = copy.deepcopy(n)
            row.update(id=len(unique),covered=False,children=[])
            unique.append(row)
    library = dict(data,nodes=unique,roots=[keys[geometry(data['nodes'][j])] for j in data['roots']])
    checker = ScalarVerifier(library)
    moves = geometry_moves(library,length,return_blocks)
    matrix = [{} for _ in unique]
    parameters = []
    contributions = []
    for i,group in enumerate(moves):
        r,s,h = tuple(rational_in(box) for box in checker.box(i))
        parameters.append(list(map(str,(r,s,h))))
        for u,v,cases in group:
            gu,iu=point_gains(u,r)
            gv,iv=point_gains(v,s)
            arrival = h*gu*iv
            swap = arrival > 1
            normalized = 1/arrival if swap else arrival
            scale = h*iv if swap else iu
            case = next(c for c in cases if c[0] == swap)
            for j in case[2]:
                lo,hi = checker.box(j)[2]
                if lo <= normalized <= hi:
                    matrix[i][j] = matrix[i].get(j,B())+scale
                    contributions.append(dict(source=i,target=j,words=[u,v],
                                              swap=swap,scale=scale.record()))
    numeric = [{j:float(a.decimal()) for j,a in row.items()} for row in matrix]
    weights = [1.0]*len(unique)
    witness = None
    for iteration in range(129):
        if iteration % 4 == 0:
            rational = [F(math.ceil(x*10**6),10**6) for x in weights]
            delta = margins(matrix,rational)
            if delta is not None:
                witness = dict(iteration=iteration,weights=list(map(str,rational)),
                               margins=[x.record() for x in delta])
                break
        weights = [1+sum(a*weights[j] for j,a in row.items()) for row in numeric]
        if not all(math.isfinite(x) and x < 10**30 for x in weights):
            break
    return dict(types=len(unique),geometry_moves=sum(map(len,moves)),length=length,
                return_blocks=return_blocks,parameters=parameters,
                geometries=[geometry(n) for n in unique],
                contributions=contributions,
                matrix=[{str(j):a.record() for j,a in row.items()} for row in matrix],
                contraction_certificate=witness,
                expansion_certificate=expansion_witness(matrix) if witness is None else None,
                status='positive-width closure impossible for this fixed return family'
                       if witness is not None else 'no width-contraction certificate found; inconclusive')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--length',type=int,default=4,choices=range(1,7))
    ap.add_argument('--no-return-blocks',action='store_true')
    args = ap.parse_args()
    result = audit(json.loads(args.source.read_text()),length=args.length,
                   return_blocks=not args.no_return_blocks)
    result['source'] = str(args.source)
    result['source_sha256'] = hashlib.sha256(args.source.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(types=result['types'],moves=result['geometry_moves'],status=result['status'])))


if __name__ == '__main__':
    main()
