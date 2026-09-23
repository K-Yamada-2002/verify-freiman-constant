#!/usr/bin/env python3
"""Find a closed strategy in a fixed library, retaining all offered alternatives.

One offered child interval may use different containing library types on
different R slabs. The full parameter image must be covered. Candidate
selection is floating point; selected rules and the supported core are
independently checked exactly before any output is certified.
"""
import argparse
from collections import defaultdict, deque
import copy
from itertools import product
import json
from pathlib import Path

from explore import extreme_tail, state_of
from search_cyclic_types import Search, fl
from type_graph_geometry import endpoint, exchange
from verify_cyclic_types import Verifier


def merge_library(graphs):
    result = dict(format='freiman-cyclic-types-v1', cells=[], nodes=[], roots={}, sources=[])
    cell_ids, node_ids, mappings = {}, {}, []
    # Types with exactly equal domains and endpoint coordinates share a node.
    for data in graphs:
        checker = Verifier(data)
        audit = checker.audit()
        if audit['failed_rules']:
            raise ValueError('invalid source rules')
        result['sources'].append(checker.proof_hash())
        mapping = []
        for node in checker.nodes:
            cell = checker.cells[node['cell']]
            if cell not in cell_ids:
                cell_ids[cell] = len(result['cells'])
                result['cells'].append(cell.record())
            key = (cell, *(endpoint(cell.states, node[k]) for k in ('lower', 'upper')))
            if key not in node_ids:
                node_ids[key] = len(result['nodes'])
                result['nodes'].append(dict(cell=cell_ids[cell], lower=node['lower'],
                                            upper=node['upper'], children=[]))
            mapping.append(node_ids[key])
        mappings.append(mapping)
    alternative_rules = defaultdict(list)
    for data, mapping in zip(graphs, mappings):
        for i, node in enumerate(data['nodes']):
            edges = [dict(e, destinations=[dict(node=mapping[d['node']], swap=d['swap'])
                     for d in e['destinations']]) for e in node.get('children', [])]
            alternative_rules[mapping[i]].extend(edges)
            if edges and not result['nodes'][mapping[i]]['children']:
                result['nodes'][mapping[i]]['children'] = edges
    result['roots'] = {k: mappings[0][v] for k, v in graphs[0]['roots'].items()}
    return result, alternative_rules


class LibrarySolver:
    def __init__(self, data, old_offers, max_step=1):
        self.data, self.old_offers, self.max_step = data, old_offers, max_step
        self.checker = Verifier(data)
        self.geometry = Search([], bins=1, outer_depth=0, local_filter=False)
        self.geometry.cells = self.checker.cells
        self.geometry.floatcells = [(tuple(map(fl, c.r)), tuple(map(fl, c.s)),
              tuple(map(fl, c.ratio)), tuple(map(fl, c.anchors()))) for c in self.checker.cells]
        self.groups = defaultdict(list)
        self.ends = []
        for i, n in enumerate(data['nodes']):
            cell = self.checker.cells[n['cell']]
            self.groups[tuple(map(state_of, cell.states)), cell.parity, cell.high].append(i)
            self.ends.append(tuple(tuple(map(fl, endpoint(cell.states, n[k]))) for k in ('lower', 'upper')))
        self.cache = {}
        self.generated = 0

    def prepare(self, index):
        if index in self.cache:
            return self.cache[index]
        node = self.data['nodes'][index]
        cid = node['cell']
        cell = self.checker.cells[cid]
        states = tuple(map(state_of, cell.states))
        geo = self.geometry
        offers = []
        for edge in self.old_offers[index]:
            a, b = (tuple(map(fl, endpoint(cell.states, edge[k], edge['suffixes']))) for k in ('lower', 'upper'))
            offers.append((a, b, edge, None))
        suffixes = []
        for total in range(1, self.max_step+1):
            for k in range(total+1):
                for letters in product('123', repeat=total):
                    u, v = ''.join(letters[:k]), ''.join(letters[k:])
                    if '31313' not in states[0]+u and '31313' not in states[1]+v:
                        suffixes.append((u, v))
        periodic = []
        for state, high in zip(states, (cell.high, cell.high if cell.parity > 0 else not cell.high)):
            _, pre, period = extreme_tail(state, high)
            periodic.append((pre+period*3)[:6])
        suffixes.append(tuple(periodic))
        for u, v in dict.fromkeys(suffixes):
            for high in (False, True):
                st, p, h, rb, sb, qb = geo.image(cid, u, v, high)
                candidates, shapes = [], {}
                for swap in (False, True):
                    signature = (st[::-1], p, h if p > 0 else not h) if swap else (st, p, h)
                    for j in self.groups[signature]:
                        dest = self.data['nodes'][j]
                        r, s, q, _ = geo.floatcells[dest['cell']]
                        if swap:
                            r, s, q = s, r, (1/q[1], 1/q[0])
                        if not all(a[0] <= b[0]+2e-14 and b[1] <= a[1]+2e-14
                                   for a, b in ((r, rb), (s, sb))):
                            continue
                        if max(q[0], qb[0]) > min(q[1], qb[1])+2e-14:
                            continue
                        labels = tuple(exchange(dest[k]) if swap else tuple(dest[k]) for k in ('lower', 'upper'))
                        xy = tuple(tuple(map(fl, endpoint(st, z))) for z in labels)
                        shapes.setdefault(tuple(sorted(xy)), labels)
                        candidates.append((j, swap, q))
                for labels in shapes.values():
                    mapped = [tuple(map(fl, endpoint(states, z, (u, v)))) for z in labels]
                    if geo.value(cid, mapped[0]) > geo.value(cid, mapped[1]):
                        labels, mapped = labels[::-1], mapped[::-1]
                    a, b = mapped
                    if geo.value(cid, b) <= geo.value(cid, a)+1e-13 or not geo.ge(cid, b, a):
                        continue
                    eligible = []
                    for j, swap, q in candidates:
                        target = self.data['nodes'][j]
                        dc = self.checker.cells[target['cell']]
                        lo, hi = self.ends[j]
                        points = [tuple(map(fl, endpoint(dc.states, exchange(z) if swap else z))) for z in labels]
                        if all(geo.ge(target['cell'], x, lo) and geo.ge(target['cell'], hi, x) for x in points):
                            eligible.append((j, swap, q))
                    if eligible:
                        edge = dict(suffixes=(u, v), high=high, lower=labels[0], upper=labels[1])
                        offers.append((a, b, edge, (qb, eligible)))
                        self.generated += 1
        # Exact duplicates add no strategy alternatives.
        result, seen = [], set()
        for offer in offers:
            key = json.dumps(offer[2:], sort_keys=True)
            if key not in seen:
                seen.add(key)
                result.append(offer)
        self.cache[index] = result
        return result

    @staticmethod
    def destinations(offer, alive):
        _, _, edge, choice = offer
        if choice is None:
            return edge['destinations'] if all(d['node'] in alive for d in edge['destinations']) else None
        (low, high), eligible = choice
        result, current = [], low
        while current < high-2e-14 or not result:
            options = [(j, swap, q) for j, swap, q in eligible if j in alive
                       and q[0] <= current+2e-14 and q[1] >= current-2e-14
                       and (q[1] > current+2e-14 or high-low <= 2e-14)]
            if not options:
                return None
            j, swap, q = max(options, key=lambda t: (t[2][1], -t[0]))
            result.append(dict(node=j, swap=swap))
            current = q[1]
            if current >= high-2e-14:
                return result
        return result

    def plan(self, index, alive):
        cid = self.data['nodes'][index]['cell']
        geo = self.geometry
        start, end = self.ends[index]
        usable = []
        for offer in self.prepare(index):
            targets = self.destinations(offer, alive)
            if targets:
                a, b, edge, _ = offer
                usable.append((a, b, dict(edge, destinations=targets)))
        usable.sort(key=lambda z: geo.value(cid, z[1]), reverse=True)
        # Exhaust all contacts, since midpoint ordering alone does not order
        # endpoints uniformly on a parameter box.
        todo, predecessor = deque([start]), {start: None}
        while todo:
            point = todo.popleft()
            if geo.ge(cid, point, end):
                path = []
                while predecessor[point] is not None:
                    previous, edge = predecessor[point]
                    path.append(edge)
                    point = previous
                return path[::-1]
            for a, b, edge in usable:
                if b in predecessor or geo.value(cid, b) <= geo.value(cid, point)+1e-13:
                    continue
                if geo.ge(cid, point, a) and geo.ge(cid, b, point):
                    predecessor[b] = (point, edge)
                    todo.append(b)
        return None

    def solve(self):
        alive = set(range(len(self.data['nodes'])))
        queue, queued = deque(sorted(alive)), set(alive)
        plans, parents = {}, defaultdict(set)
        steps = 0
        while queue:
            i = queue.popleft()
            queued.remove(i)
            if i not in alive:
                continue
            plan = self.plan(i, alive)
            steps += 1
            for e in plans.get(i, []):
                for d in e['destinations']:
                    parents[d['node']].discard(i)
            if plan is None:
                alive.remove(i)
                plans.pop(i, None)
                for p in tuple(parents[i]):
                    if p in alive and p not in queued:
                        queue.append(p)
                        queued.add(p)
            else:
                plans[i] = plan
                for e in plan:
                    for d in e['destinations']:
                        parents[d['node']].add(i)
            if steps % 100 == 0:
                print(json.dumps(dict(steps=steps, alive=len(alive), pending=len(queue),
                                      offers=self.generated)), flush=True)
        for i in alive:
            self.data['nodes'][i]['children'] = plans[i]
        self.checker.checked.clear()
        for i in alive:
            rule = self.checker.local(i)
            if not set(rule['dependencies']) <= alive:
                raise ValueError('supported core has an open dependency')
        return dict(supported=sorted(alive), steps=steps, generated_offers=self.generated)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graphs', type=Path, nargs='+')
    ap.add_argument('--max-step', type=int, default=1)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    data, old = merge_library([json.loads(p.read_text()) for p in args.graphs])
    solver = LibrarySolver(data, old, args.max_step)
    result = solver.solve()
    data['library_search'] = result
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    checker = Verifier(data)
    audit = checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    try:
        verified = checker.closed()
    except ValueError as error:
        verified = dict(closed=False, reason=str(error))
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(verified, indent=2)+'\n')
    print(json.dumps(dict(nodes=len(data['nodes']), supported=len(result['supported']),
                          failed=len(audit['failed_rules']), verification=verified)), flush=True)


if __name__ == '__main__':
    main()
