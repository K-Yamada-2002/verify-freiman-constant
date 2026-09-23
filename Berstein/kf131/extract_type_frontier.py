#!/usr/bin/env python3
"""Keep a bounded connected set of local rules, exposing all other nodes as open.

This reduces a large unfinished certificate without hiding its obligations.
The source checksum and original counts remain in the extracted file.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from verify_type_graph import Verifier
from verify_scalar_graph import ScalarVerifier


def dependencies(node):
    for edge in node['children']:
        if 'cases' in edge:
            for case in edge['cases']:
                yield from case['destinations']
        else:
            yield from (dest['node'] for dest in edge['destinations'])


def extract(data, local_budget):
    if local_budget < 0:
        raise ValueError('nonnegative local rule budget required')
    queue = list(dict.fromkeys(data['roots']))
    seen = set(queue)
    retained, nodes = 0, {}
    position = 0
    while position < len(queue):
        index = queue[position]
        position += 1
        node = copy.deepcopy(data['nodes'][index])
        if node['covered'] and retained < local_budget:
            retained += 1
            for child in dependencies(node):
                if child not in seen:
                    seen.add(child)
                    queue.append(child)
        else:
            node['covered'] = False
            node['children'] = []
        nodes[index] = node
    ids = {old: new for new, old in enumerate(queue)}
    for old, node in nodes.items():
        node['id'] = ids[old]
        for edge in node['children']:
            if 'cases' in edge:
                for case in edge['cases']:
                    case['destinations'] = [ids[j] for j in case['destinations']]
            else:
                for destination in edge['destinations']:
                    destination['node'] = ids[destination['node']]
    result = {key: value for key, value in data.items() if key != 'nodes'}
    result.update(nodes=[nodes[j] for j in queue], roots=[ids[j] for j in data['roots']],
                  open_nodes=len(queue)-retained,
                  closed_candidate=bool(queue) and retained == len(queue),
                  status='extracted local rules; discarded continuations remain explicit open obligations')
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path)
    ap.add_argument('--local-rules', type=int, default=128)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--audit', action='store_true')
    args = ap.parse_args()
    raw = args.source.read_bytes()
    data = json.loads(raw)
    result = extract(data, args.local_rules)
    result['extraction'] = dict(source_sha256=hashlib.sha256(raw).hexdigest(),
                                source_nodes=len(data['nodes']),
                                source_open_nodes=data['open_nodes'], local_rule_budget=args.local_rules)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(retained_rules=sum(n['covered'] for n in result['nodes']),
                          open_nodes=result['open_nodes'], nodes=len(result['nodes']))), flush=True)
    if args.audit:
        checker = (ScalarVerifier if data.get('schema', '').startswith('kf131-scalar-') else Verifier)(result)
        audit = checker.audit()
        path = args.output.with_suffix('.audit.json')
        path.write_text(json.dumps(audit, indent=2)+'\n')
        print(json.dumps(dict(verified_rules=len(audit['verified_rules']),
                              failed_rules=len(audit['failed_rules']),
                              open_nodes=len(audit['open_nodes']))), flush=True)
        if audit['failed_rules']:
            raise SystemExit('exact local audit failed')


if __name__ == '__main__':
    main()
