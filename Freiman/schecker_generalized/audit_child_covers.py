#!/usr/bin/env python3
"""Replay uniform child covers and expose every unresolved family obligation.

This is a closure audit, not a filledness certificate. Even a closed graph
would additionally require shrinkage along its infinite paths.
"""
import argparse
import json
from pathlib import Path
from child_family_covers import verify_row


def canonical(u, v, kind):
    # (U_n 131213, V_n 313121) = (U_{n+1}, V_{n+1}).
    while u.startswith('131213') and v.startswith('313121'):
        u, v = u[6:], v[6:]
    return u, v, kind


def audit(documents, obstructions=()):
    rows = {}
    for data in sorted(documents, key=lambda d: d.get('rule_priority', d['lookahead_used_only_for_discovery'])):
        for row in data['covers']:
            verify_row(row)
            # A rule only for n>=1 does not discharge an n>=0 obligation.
            if row['n_range'] != 'all n>=0':
                continue
            key = (row['left_suffix'], row['right_suffix'], row['kind'])
            rows[key] = row
    pending = [('1', '', 0), ('2', '', 0), ('', '1', 4)]
    seen, missing, edges = set(), set(), []
    while pending:
        key = canonical(*pending.pop())
        if key in seen:
            continue
        seen.add(key)
        if key not in rows:
            missing.add(key)
            continue
        row = rows[key]
        u, v, _ = key
        for child in row['children']:
            a, b = child['suffixes']
            target = canonical(u+a, v+b, child['kind'])
            edges.append((key, target))
            pending.append(target)
    # A valid local cover may still ask a child to fill an impossible interval.
    if obstructions:
        from frontier_obstructions import verify_gap
    refuted = []
    for obstruction in obstructions:
        verify_gap(obstruction)
        key = (obstruction['left_suffix'], obstruction['right_suffix'], obstruction['kind'])
        if key in seen:
            refuted.append(key)
    return {'status': 'closure audit only; no filledness assertion',
            'verified_available_rules': len(rows),
            'reachable_rules': len(seen - missing),
            'unproved_frontier': sorted(missing),
            'closed_under_children': not missing,
            'known_refuted_obligations': sorted(set(refuted)),
            'edges': edges}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='+', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--obstructions', type=Path)
    args = parser.parse_args()
    obstructions = (json.loads(args.obstructions.read_text())['obstructions']
                    if args.obstructions else ())
    result = audit([json.loads(p.read_text()) for p in args.files], obstructions)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'edges'}, indent=2))
