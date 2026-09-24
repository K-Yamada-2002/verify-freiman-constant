#!/usr/bin/env python3
"""Pool compatible discovery dictionaries, preserving all complete rule choices."""
import argparse
import copy
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path

from audit_alternative_bank import supported
from extract_type_frontier import dependencies
from verify_scalar_graph import ScalarVerifier


def type_key(node):
    return (tuple(node['states']),node['parity'],node['ratio_bin'],
            tuple(node.get('ratio_refinement',[0,0])),tuple(node['interval']))


def merge(banks):
    # Accept a one-pass iterator so large source dictionaries need not coexist.
    out=None
    ids, signatures = {}, set()
    for data in banks:
        if out is None:
            out={k:copy.deepcopy(data[k]) for k in ('schema','settings','root_prefixes')}
            out.update(nodes=[],alternative_rules=[],roots=[],closed_candidate=False)
        if data['schema'] != out['schema'] or data['root_prefixes'] != out['root_prefixes']:
            raise ValueError('incompatible schema or physical root prefixes')
        for k in ('base','bins','grid'):
            if Fraction(str(data['settings'][k])) != Fraction(str(out['settings'][k])):
                raise ValueError('incompatible geometry: '+k)
        out['settings']['memory']=max(out['settings']['memory'],data['settings']['memory'])
        out['settings']['max_step']=max(out['settings']['max_step'],data['settings']['max_step'])
        mapping={}
        for i,node in enumerate(data['nodes']):
            if node['id'] != i: raise ValueError('nonconsecutive input IDs')
            key=type_key(node)
            if key not in ids:
                ids[key]=len(out['nodes'])
                new=copy.deepcopy({k:v for k,v in node.items() if k!='children'})
                new.update(id=ids[key],covered=False,children=[])
                out['nodes'].append(new)
            mapping[i]=ids[key]
        if not out['roots']: out['roots']=[mapping[i] for i in data['roots']]
        def remap(edges):
            result=copy.deepcopy(edges)
            for edge in result:
                for case in edge['cases']:
                    case['destinations']=[mapping[i] for i in case['destinations']]
            return result
        rules=list(data.get('alternative_rules',[]))
        for node in data['nodes']:
            if node['covered']:
                parent=mapping[node['id']]
                if not out['nodes'][parent]['covered']:
                    out['nodes'][parent].update(covered=True,children=remap(node['children']))
                rules.append(dict(parent=node['id'],children=node['children']))
        for rule in rules:
            parent=mapping[rule['parent']]
            signature=(parent,tuple(sorted({mapping[i] for i in dependencies(rule)})))
            if signature in signatures: continue
            signatures.add(signature)
            out['alternative_rules'].append(dict(parent=parent,children=remap(rule['children'])))
        del data, rules
    if out is None:
        raise ValueError('at least one source dictionary is required')
    out['open_nodes']=sum(not n['covered'] for n in out['nodes'])
    out['status']='union of provisional rule banks; exact closure verification required'
    return out


def merge_history(paths, output):
    """Pool heuristic counts by maximum; shared prior work is not added twice."""
    header=None; counts={}
    for path in paths:
        with path.open() as stream:
            current=stream.readline().strip()
            if not current: raise ValueError('empty history')
            if header is not None and header!=current: raise ValueError('history geometry mismatch')
            header=current
            for line in stream:
                if not line.strip(): continue
                fields=line.split()
                if len(fields)!=9: raise ValueError('malformed history key')
                key=tuple(fields[:-1]); count=int(fields[-1])
                if count<0: raise ValueError('negative history count')
                counts[key]=max(counts.get(key,0),count)
    if header is None: raise ValueError('at least one history is required')
    output.write_text(header+'\n'+''.join(
        ' '.join(key)+' '+str(value)+'\n' for key,value in sorted(counts.items())))
    return len(counts)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('sources',type=Path,nargs='+')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--learning',type=Path,nargs='*',default=[])
    ap.add_argument('--global-history',type=Path,nargs='*',default=[])
    args=ap.parse_args()
    manifests=[]
    def sources():
        for path in args.sources:
            raw=path.read_bytes()
            manifests.append(dict(path=str(path),sha256=hashlib.sha256(raw).hexdigest()))
            data=json.loads(gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw)
            del raw
            yield data
            del data
    result=merge(sources())
    result['merged_sources']=manifests
    core=supported(result)
    if result['roots'][0] in core['supported_nodes']:
        alive=set(core['supported_nodes'])
        installed=set()
        for rule in result['alternative_rules']:
            parent=rule['parent']
            if parent in alive and parent not in installed and set(dependencies(rule))<=alive:
                result['nodes'][parent].update(covered=True,children=rule['children'])
                installed.add(parent)
        # No combinatorial flag can substitute for number-field verification.
        proof=ScalarVerifier(result).closed()
        result['closed_candidate']=True
        args.output.with_suffix('.proof.json').write_text(json.dumps(proof,indent=2)+'\n')
    result['open_nodes']=sum(not n['covered'] for n in result['nodes'])
    raw=(json.dumps(result,separators=(',',':'))+'\n').encode()
    args.output.write_bytes(gzip.compress(raw,compresslevel=6,mtime=0)
                           if args.output.suffix=='.gz' else raw)
    core.update(output_sha256=hashlib.sha256(args.output.read_bytes()).hexdigest(),sources=manifests)
    args.output.with_suffix('.core.json').write_text(json.dumps(core,indent=2)+'\n')
    if args.learning:
        merge_history(args.learning,args.output.with_suffix('.learning.txt'))
    if args.global_history:
        merge_history(args.global_history,args.output.with_suffix('.global.txt'))
    print(json.dumps(core),flush=True)


if __name__=='__main__': main()
