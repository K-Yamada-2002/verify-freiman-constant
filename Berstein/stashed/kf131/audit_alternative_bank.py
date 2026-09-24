#!/usr/bin/env python3
"""Recompute finite AND/OR support and exactly audit a bounded rule sample."""
import argparse
from collections import deque
import copy
import gzip
import hashlib
import json
from pathlib import Path

from extract_type_frontier import dependencies
from verify_scalar_graph import ScalarVerifier


def supported(data):
    n = len(data['nodes'])
    rules = data['alternative_rules']
    count, incoming = [0]*n, [[] for _ in range(n)]
    for i, rule in enumerate(rules):
        count[rule['parent']] += 1
        for child in set(dependencies(rule)):
            incoming[child].append(i)
    alive = [c > 0 for c in count]
    queue = deque(i for i, a in enumerate(alive) if not a)
    active = [True]*len(rules)
    while queue:
        child = queue.popleft()
        for i in incoming[child]:
            if not active[i]: continue
            active[i] = False
            parent = rules[i]['parent']
            count[parent] -= 1
            if count[parent] == 0 and alive[parent]:
                alive[parent] = False
                queue.append(parent)
    alternatives = [0]*n
    for rule in rules: alternatives[rule['parent']] += 1
    return dict(types=n, retained_rules=len(rules),
                types_with_multiple_rules=sum(c > 1 for c in alternatives),
                maximum_rules_per_type=max(alternatives, default=0),
                supported_nodes=[i for i,a in enumerate(alive) if a],
                scope='all retained rules; no floating-point negative filters applied')


def sample(data, limit, minimum_memory=0, first_rule=0):
    chosen = {}
    # Prefer rules different from the final selection, including discarded
    # choices at types that are no longer reachable from the current root.
    rules = sorted(enumerate(data['alternative_rules']), key=lambda pair:
                   pair[1]['children'] == data['nodes'][pair[1]['parent']]['children'])
    for rule_id, rule in rules:
        if rule_id < first_rule: continue
        if len(chosen) >= limit: break
        related = [rule['parent']] + list(dependencies(rule))
        if max(len(w) for i in related for w in data['nodes'][i]['states']) < minimum_memory:
            continue
        chosen.setdefault(rule['parent'], (rule_id, rule))
    keep = set(data['roots']) | set(chosen)
    for _, rule in chosen.values(): keep.update(dependencies(rule))
    order = list(data['roots']) + sorted(keep-set(data['roots']))
    ids = {old:new for new,old in enumerate(order)}
    result = {key:copy.deepcopy(value) for key,value in data.items()
              if key not in ('nodes','alternative_rules')}
    result['nodes'] = []
    for old in order:
        node = copy.deepcopy(data['nodes'][old])
        node.update(id=ids[old],covered=old in chosen,
                    children=copy.deepcopy(chosen[old][1]['children']) if old in chosen else [])
        for edge in node['children']:
            for case in edge['cases']:
                case['destinations'] = [ids[i] for i in case['destinations']]
        result['nodes'].append(node)
    result.update(roots=[ids[i] for i in data['roots']],closed_candidate=False,
                  open_nodes=len(order)-len(chosen),
                  status='sample of retained alternatives; all other obligations left open',
                  sampled_alternative_ids=[r[0] for r in chosen.values()],
                  sampled_discarded_rules=sum(rule['children'] != data['nodes'][parent]['children']
                                              for parent,(_,rule) in chosen.items()))
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--rules',type=int,default=64)
    ap.add_argument('--core-only',action='store_true')
    ap.add_argument('--minimum-memory',type=int,default=0)
    ap.add_argument('--first-rule',type=int,default=0)
    args = ap.parse_args()
    raw=args.source.read_bytes()
    data=json.loads(gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw)
    core=supported(data)
    core['source_sha256']=hashlib.sha256(raw).hexdigest()
    args.output.with_suffix('.core.json').write_text(json.dumps(core,indent=2)+'\n')
    print(json.dumps(core),flush=True)
    if args.core_only: return
    chosen=sample(data,args.rules,args.minimum_memory,args.first_rule)
    chosen['source_catalog_sha256']=core['source_sha256']
    args.output.write_text(json.dumps(chosen,indent=2)+'\n')
    audit=ScalarVerifier(chosen).audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps(dict(verified=len(audit['verified_rules']),failed=len(audit['failed_rules']),
                          discarded=chosen['sampled_discarded_rules'])),flush=True)
    if audit['failed_rules']: raise SystemExit('exact rule audit failed')


if __name__=='__main__': main()
