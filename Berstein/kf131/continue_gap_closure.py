#!/usr/bin/env python3
"""Expand pending exact interval obligations and seek genuine coinductive closure.

The initial frontier is exhausted before descendants receive priority. Every
batch keeps the old roots and validates the merged graph. Existing interval
types can be reused only with full parameter-box and scalar coverage.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path

from add_gap_repair_moves import add_moves
from closure_diagnostics import deletion_ranks
from extract_type_frontier import dependencies
from graft_gap_repairs import geometry,graft
from repair_gap_intervals import repair
from exact import F,state_of
from scalar_obstructions import replay
from verify_scalar_graph import ScalarVerifier
from coalesce_open_types import coalesce


def key(node):
    return json.dumps([geometry(node),node['interval']],separators=(',',':'))


def graph_status(data):
    ranks = deletion_ranks(dict(data,alternative_rules=[dict(parent=j,children=n['children'])
                              for j,n in enumerate(data['nodes']) if n['covered']]))
    return dict(nodes=len(data['nodes']),local_rules=sum(n['covered'] for n in data['nodes']),
                open_nodes=sum(not n['covered'] for n in data['nodes']),
                supported_nodes=[j for j,r in enumerate(ranks) if r is None],
                root_ranks=[ranks[j] for j in data['roots']])


def refuted_roots(data, certificates):
    """Reject fixed roots contradicted by an independently replayed witness."""
    verifier = ScalarVerifier(data)
    result = []
    for j in data['roots']:
        node = data['nodes'][j]
        lo,hi = verifier.interval(node['interval'])
        for cert in certificates:
            other = cert['type']
            if node['parity'] != other['parity'] or tuple(map(state_of,node['states'])) != tuple(map(state_of,other['states'])):
                continue
            if not lo <= F(cert['target']) <= hi:
                continue
            if not all(a <= F(t) <= b for t,(a,b) in zip(cert['parameters'],verifier.box(j))):
                continue
            replay(cert)
            result.append(dict(root=j,target=cert['target'],parameters=cert['parameters']))
            break
    return result


def backtrack_refuted_children(data, certificates):
    """Discard chosen implications using a false premise, not the parent claim.

    A refuted parent cannot be repaired by changing its children. Its incoming
    implications must be replaced instead. Never infer parent falsity from a
    false child; only an exact witness can refute a type.
    """
    all_nodes = dict(data,roots=list(range(len(data['nodes']))))
    bad = {r['root'] for r in refuted_roots(all_nodes,certificates)}
    if bad.intersection(data['roots']):
        raise ValueError('a fixed root is refuted; revise the root itself')
    result = copy.deepcopy(data)
    retry = []
    for node in result['nodes']:
        if node['covered'] and bad.intersection(dependencies(node)):
            retry.append(key(node))
            node.update(covered=False,children=[])
    result,_ = graft(result,result)
    return result,retry,sorted(bad)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph',type=Path)
    ap.add_argument('--obstructions',type=Path,required=True)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--batches',type=int,default=16)
    ap.add_argument('--batch-size',type=int,default=8)
    ap.add_argument('--length',type=int,default=3)
    ap.add_argument('--sieve-budget',type=int,default=300)
    ap.add_argument('--history',type=Path)
    ap.add_argument('--whole-depth',type=int,default=7)
    ap.add_argument('--memory',type=int,default=7)
    ap.add_argument('--refinement',type=int,default=3)
    ap.add_argument('--local-envelopes',action='store_true')
    ap.add_argument('--coalesce',action='store_true')
    ap.add_argument('--library-fragments',action='store_true')
    ap.add_argument('--prefer-reuse',action='store_true')
    args = ap.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    current = json.loads(args.graph.read_text())
    bank = json.loads(args.obstructions.read_text())['obstructions']
    refutations = refuted_roots(current,bank)
    if refutations:
        report = dict(status='fixed root assertions are false; revise intervals or parameter boxes',
                      refuted_roots=refutations,closed=False)
        (args.output_dir/'blocked_roots.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report),flush=True)
        return
    initial = {key(n) for n in current['nodes'] if not n['covered']}
    history = json.loads(args.history.read_text()) if args.history else {}
    seen = set(history.get('attempted_keys',[]))
    source_hash = hashlib.sha256(args.graph.read_bytes()).hexdigest()
    log = dict(source_sha256=source_hash,initial_obligations=len(initial),batches=[])
    for batch in range(args.batches):
        if args.coalesce:
            current,fold = coalesce(current)
            if fold['merges']:
                print(json.dumps(dict(coalesced=fold)),flush=True)
        current,retry,bad = backtrack_refuted_children(current,bank)
        seen.difference_update(retry)
        if bad:
            print(json.dumps(dict(backtrack_refuted_nodes=bad,retry_parents=len(retry))),flush=True)
        current,_ = graft(current,current)
        references = Counter(j for n in current['nodes'] if n['covered'] for j in dependencies(n))
        pending = [n['id'] for n in current['nodes'] if not n['covered'] and key(n) not in seen]
        pending.sort(key=lambda j:(key(current['nodes'][j]) not in initial,-references[j],j))
        targets = pending[:args.batch_size]
        if not targets:
            break
        before = graph_status(current)
        incoming = dict(settings=current['settings'],nodes={str(n['id']):copy.deepcopy(n) for n in current['nodes']},
                        parents={str(j):[] for j in targets},rules=[],source_graph=str(args.graph),source_sha256=source_hash)
        # Existing uniform rules on the same box may cover a new interval.
        for j in targets:
            for n in current['nodes']:
                if n['covered'] and geometry(n) == geometry(current['nodes'][j]):
                    incoming['rules'].append(dict(parent=j,children=copy.deepcopy(n['children']),source_rule=n['id']))
        prefix = args.output_dir/f'batch_{batch+1:03}'
        print(json.dumps(dict(batch=batch+1,targets=targets,before=before)),flush=True)
        add_moves(incoming,targets,args.length,memory=args.memory,refinement=args.refinement)
        prefix.with_suffix('.incoming.json').write_text(json.dumps(incoming,separators=(',',':'))+'\n')
        patch,report = repair(incoming,bank,grid=current['settings']['grid'],expand_offers=True,
                              sieve_budget=args.sieve_budget,reuse_types=True,whole_depth=args.whole_depth,
                              local_envelopes=args.local_envelopes,use_library_fragments=args.library_fragments,
                              prefer_reuse=args.prefer_reuse)
        prefix.with_suffix('.patch.json').write_text(json.dumps(patch,separators=(',',':'))+'\n')
        prefix.with_suffix('.repair.json').write_text(json.dumps(report,separators=(',',':'))+'\n')
        for j in targets:
            seen.add(key(current['nodes'][j]))
        current,merge_report = graft(current,patch)
        bank.extend(report['discovered_obstructions'])
        after = graph_status(current)
        row = dict(batch=batch+1,targets=len(targets),repaired=len(report['repaired']),
                   failed=len(report['failed']),reused_requests=report['reused_requests'],
                   new_obstructions=len(report['discovered_obstructions']),before=before,after=after)
        log['batches'].append(row)
        log['attempted_keys'] = sorted(seen)
        log['initial_unattempted'] = sum(not n['covered'] and key(n) in initial and key(n) not in seen
                                         for n in current['nodes'])
        (args.output_dir/'current.json').write_text(json.dumps(current,indent=2)+'\n')
        (args.output_dir/'obstructions.json').write_text(json.dumps(dict(obstructions=bank),separators=(',',':'))+'\n')
        (args.output_dir/'history.json').write_text(json.dumps(log,indent=2)+'\n')
        print(json.dumps(row),flush=True)
        if after['supported_nodes']:
            print('Closed combinatorial component found. A physical seed and exact closed verification are still required.',flush=True)
            break


if __name__ == '__main__':
    main()
