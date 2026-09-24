#!/usr/bin/env python3
"""Deletion ranks for all retained AND/OR rules; not a geometric proof.

A finite rank is the last finite horizon the saved rules can support:
rank(t)=0 with no rule, otherwise 1+max_rule min_child rank(child).
None denotes membership in the greatest fixed point. No negative numerical
filter is used. A rank is not a distance to a completed proof.
"""
import argparse
from collections import Counter, deque
import gzip
import hashlib
import json
from pathlib import Path

from extract_type_frontier import dependencies


def deletion_ranks(data):
    n = len(data['nodes'])
    rules = data['alternative_rules']
    incoming = [[] for _ in range(n)]
    remaining = [0]*n
    for i, rule in enumerate(rules):
        remaining[rule['parent']] += 1
        for child in set(dependencies(rule)):
            incoming[child].append(i)
    ranks = [None]*n
    queue = deque()
    for i, count in enumerate(remaining):
        if count == 0:
            ranks[i] = 0
            queue.append(i)
    killed = [False]*len(rules)
    last = [0]*n
    while queue:
        child = queue.popleft()
        for i in incoming[child]:
            if killed[i]:
                continue
            killed[i] = True
            parent = rules[i]['parent']
            remaining[parent] -= 1
            last[parent] = max(last[parent], ranks[child]+1)
            if remaining[parent] == 0:
                ranks[parent] = last[parent]
                queue.append(parent)
    return ranks


def summarize(data, ranks, limit=32):
    nodes, rules = data['nodes'], data['alternative_rules']
    references = Counter()
    single_open = Counter()
    rule_widths = Counter()
    for rule in rules:
        children = set(dependencies(rule))
        rule_widths[len(children)] += 1
        missing = [i for i in children if ranks[i] == 0]
        references.update(missing)
        if len(missing) == 1:
            single_open.update(missing)
    def record(i):
        return dict(node=i, rank=ranks[i],
                    type={k:v for k,v in nodes[i].items()
                          if k not in ('children','covered','id')},
                    direct_references=references[i],
                    rules_with_this_only_unexpanded_child=single_open[i])
    finite = [i for i,r in enumerate(ranks) if r is not None]
    return dict(settings=dict(base=str(data['settings']['base']),bins=data['settings']['bins'],
                              grid=data['settings']['grid']),types=len(nodes), rules=len(rules),
                supported=sum(r is None for r in ranks),
                root_ranks={str(i):ranks[i] for i in data['roots']},
                deletion_rank_histogram=dict(sorted(Counter(ranks[i] for i in finite).items())),
                dependency_count_histogram=dict(sorted(rule_widths.items())),
                deepest=[record(i) for i in sorted(finite,key=lambda i:(-ranks[i],i))[:limit]],
                most_shared_unexpanded=[record(i) for i,_ in references.most_common(limit)],
                one_missing=[record(i) for i,_ in single_open.most_common(limit)],
                scope='all retained rules, no geometric rejection; finite ranks do not disprove interval inclusion')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--limit',default=32,type=int)
    args = ap.parse_args()
    raw = args.source.read_bytes()
    data = json.loads(gzip.decompress(raw) if raw[:2] == b'\x1f\x8b' else raw)
    result = summarize(data,deletion_ranks(data),args.limit)
    result['source_sha256'] = hashlib.sha256(raw).hexdigest()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('types','rules','supported','root_ranks','deletion_rank_histogram')}),flush=True)


if __name__ == '__main__':
    main()
