#!/usr/bin/env python3
"""Floating discovery with all one-digit endpoint pairs and interval components.

No filledness assertion: any nonempty fixed point needs an exact replay.
Unlike a fixed shape bank, endpoint types are inferred from retained components.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path

import invariant_boxes as ib
from explore import matrix


@lru_cache(None)
def side_pool(state):
    return tuple(sorted({float(ib.tail_endpoint(state, a, h).decimal())
                         for a in '123' for h in (False, True)
                         if ib.tail_endpoint(state, a, h) is not None}))


@lru_cache(None)
def pool(s, t):
    return tuple((x, y) for x in side_pool(s) for y in side_pool(t))


@lru_cache(None)
def mapped_pool(s, t, u, v):
    ss, tt = ib.suffix_state(s+u), ib.suffix_state(t+v)
    a, b, c, d = matrix(u)
    aa, bb, cc, dd = matrix(v)
    return tuple(((a*x+b)/(c*x+d), (aa*y+bb)/(cc*y+dd))
                 for x, y in pool(ss, tt))


class ComponentSearch:
    def __init__(self, bins=25, base=.88, max_step=2):
        self.qboxes = tuple((base**(i+1), base**i) for i in range(bins))
        self.max_step = max_step
        self.cells = [(s, t, p, qi) for s in ib.STATES for t in ib.STATES
                      for p in (1, -1) for qi in range(bins)]
        self.ranges = {s: tuple(map(float, r)) for s, r in zip(ib.STATES, ib.RANGES)}
        self.index = {c: i for i, c in enumerate(self.cells)}
        self.domains = []
        self.offers = []
        self.order = []
        for cell in self.cells:
            s, t, p, qi = cell
            points = pool(s, t)
            order = sorted(range(len(points)), key=lambda i: self.value(cell, points[i]))
            self.order.append(order)
            self.domains.append(((order[0], order[-1]),))
            moves = []
            for u, v in ib.suffix_pairs(s, t, max_step):
                deps = self.dependencies(cell, u, v)
                if deps:
                    moves.append((u, v, deps, mapped_pool(s, t, u, v)))
            self.offers.append(moves)

    def value(self, cell, z):
        s, t, p, qi = cell
        r = sum(self.ranges[s])/2
        ss = sum(self.ranges[t])/2
        q = sum(self.qboxes[qi])/2
        x, y = z
        return x/(1+r*x)+p*q*y/(1+ss*y)

    def ge(self, cell, a, b):
        if a == b:
            return True
        s, t, p, qi = cell
        x, y = a
        xx, yy = b
        dr, ds = x-xx, p*(y-yy)
        r = self.ranges[s][1 if dr >= 0 else 0]
        ss = self.ranges[t][1 if ds >= 0 else 0]
        q = self.qboxes[qi][0 if ds >= 0 else 1]
        return dr/((1+r*x)*(1+r*xx))+q*ds/((1+ss*y)*(1+ss*yy)) >= -1e-13

    def dependencies(self, cell, u, v):
        s, t, p, qi = cell
        rb, sb, qb = self.ranges[s], self.ranges[t], self.qboxes[qi]
        _, b, _, d = matrix(u)
        _, bb, _, dd = matrix(v)
        lo = qb[0]*(rb[0]*b+d)**2/(sb[1]*bb+dd)**2
        hi = qb[1]*(rb[1]*b+d)**2/(sb[0]*bb+dd)**2
        if lo < self.qboxes[-1][0] or hi > 1/self.qboxes[-1][0]:
            return None
        ss, tt = ib.suffix_state(s+u), ib.suffix_state(t+v)
        pp = p*(-1)**(len(u)+len(v))
        ranges = []
        if lo <= 1:
            ranges.append((ss, tt, lo, min(hi, 1), False))
        if hi >= 1:
            ranges.append((tt, ss, 1/hi, min(1/lo, 1), True))
        out = []
        for a, b, l, h, swap in ranges:
            mapping = {z: i for i, z in enumerate(pool(a, b))}
            ids = tuple(mapping[z[::-1] if swap else z] for z in pool(ss, tt))
            for j, (low, high) in enumerate(self.qboxes):
                if low <= h+1e-14 and high >= l-1e-14:
                    out.append((self.index[a, b, pp, j], ids))
        return tuple(out)

    def memberships(self, domains):
        answer = []
        for cell, components in zip(self.cells, domains):
            points = pool(*cell[:2])
            answer.append(tuple(next((j for j, (a, b) in enumerate(components)
                                      if self.ge(cell, z, points[a]) and
                                      self.ge(cell, points[b], z)), -1)
                                for z in points))
        return answer

    def update(self, cid, memberships):
        cell = self.cells[cid]
        points = pool(*cell[:2])
        offers = []
        for u, v, deps, mapped in self.offers[cid]:
            groups = defaultdict(list)
            for i in range(len(mapped)):
                signature = tuple(memberships[d][ids[i]] for d, ids in deps)
                if -1 not in signature:
                    groups[signature].append(i)
            for group in groups.values():
                if len(group) < 2:
                    continue
                group.sort(key=lambda i: self.value(cell, mapped[i]))
                lo, hi = mapped[group[0]], mapped[group[-1]]
                if self.ge(cell, hi, lo):
                    offers.append((self.value(cell, lo), self.value(cell, hi), lo, hi))
        offers.sort()
        components = []
        for _, _, lo, hi in offers:
            if components and self.ge(cell, components[-1][1], lo):
                if self.ge(cell, hi, components[-1][1]):
                    components[-1] = (components[-1][0], hi)
            else:
                components.append((lo, hi))
        result = []
        # Keep the update monotone by also restricting to each old component.
        for old_a, old_b in self.domains[cid]:
            for lo, hi in components:
                ids = [i for i in self.order[cid]
                       if self.ge(cell, points[i], lo) and self.ge(cell, hi, points[i])
                       and self.ge(cell, points[i], points[old_a])
                       and self.ge(cell, points[old_b], points[i])]
                if len(ids) > 1 and self.ge(cell, points[ids[-1]], points[ids[0]]):
                    result.append((ids[0], ids[-1]))
        # Intersecting overlapping old and new components can produce the
        # identical endpoint pair repeatedly. Keep its first occurrence;
        # duplicates carry the same interval and the same obligations.
        return tuple(dict.fromkeys(result))

    def run(self, rounds=40):
        history = []
        for iteration in range(rounds):
            memberships = self.memberships(self.domains)
            new = [self.update(i, memberships) if d else ()
                   for i, d in enumerate(self.domains)]
            changed = sum(a != b for a, b in zip(self.domains, new))
            row = {'round': iteration, 'nonempty_cells': sum(bool(d) for d in new),
                   'components': sum(map(len, new)), 'changed': changed}
            print(row, flush=True)
            history.append(row)
            self.domains = new
            if not changed:
                break
        return {'status': 'floating discovery only; requires exact verification',
                'nonempty_fixed_point': bool(any(self.domains) and not history[-1]['changed']),
                'history': history,
                'survivors': [{'cell': c, 'endpoints': [list(pool(*c[:2])[i])
                                                       for pair in d for i in pair]}
                              for c, d in zip(self.cells, self.domains) if d]}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--bins', type=int, default=25)
    ap.add_argument('--base', type=float, default=.88)
    ap.add_argument('--max-step', type=int, default=2)
    ap.add_argument('--rounds', type=int, default=40)
    ap.add_argument('--states', type=int, choices=(6, 13), default=6)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    if args.states == 13:
        ib.STATES, ib.RANGES = ib.STATES13, ib.RANGES13
    search = ComponentSearch(args.bins, args.base, args.max_step)
    print('prepared', len(search.cells), 'cells', flush=True)
    result = search.run(args.rounds)
    result['settings'] = vars(args) | {'output': str(args.output)}
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
