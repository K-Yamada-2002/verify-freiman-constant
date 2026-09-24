#!/usr/bin/env python3
"""Demand-driven cyclic type search; a successful candidate is checked exactly.

The endpoint menu is finite during one run; the interval TYPES are registered
as needed, including previously unseen pairs of endpoints. No depth limit is
used. Float comparisons propose rules; verify_cyclic_types is the proof gate.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import subprocess
import time

from explore import Q, extreme_tail, matrix, state_of, transform
import invariant_boxes as ib
from finite_type_game import Game
from cover_optimization import minimum_cover_chain
from type_graph_geometry import (Cell, anchor, endpoint, exchange, full_labels,
                                 root_cells, shape_image)
from verify_cyclic_types import Verifier


def fl(x):
    return float(Q.coerce(x).decimal())


@lru_cache(None)
def outer_tail_intervals(state, depth):
    result = []
    for letters in product('123', repeat=depth):
        word = ''.join(letters)
        if '31313' in state+word:
            continue
        end = state_of(state+word)
        a, b, c, d = matrix(word)
        values = []
        for high in (False, True):
            x = fl(anchor(end, high))
            values.append((a*x+b)/(c*x+d))
        result.append((min(values), max(values)))
    return tuple(result)


def edge_labels(denominator):
    if denominator <= 0:
        return []
    result = []
    for i in range(denominator+1):
        weight = '@'+str(F(i, denominator))
        for end in ('@0', '@1'):
            result.extend(((weight, False, end, False), (end, False, weight, False)))
    return result


class Search:
    def __init__(self, labels, states=6, bins=25, base=F(22, 25), max_step=2, variants=4,
                 outer_depth=3, reuse=True, local_filter=True, outer_samples=1, memory=0,
                 prune_supersets=False, balance=0, return_offers=True, reuse_pending=False,
                 macro_menu=None, shape_menu=None, adaptive_shapes=False, max_shapes=64,
                 min_cost_cover=False):
        self.max_step, self.variants = max_step, variants
        self.outer_depth = outer_depth
        self.outer_samples = outer_samples
        self.outer_rejections = 0
        self.base, self.bins = base, bins
        self.game = None
        self.native_executable = None
        self.native_process = None
        self.prune_supersets = prune_supersets
        self.failed_intervals = defaultdict(list)
        self.superset_rejections = 0
        self.balance = float(balance)
        self.macro_menu = macro_menu or {}
        self.shape_menu = None if shape_menu is None else tuple(dict.fromkeys(
            tuple(map(tuple, shape)) for pair in shape_menu
            for shape in (pair, tuple(exchange(z) for z in pair))))
        self.adaptive_shapes, self.max_shapes = adaptive_shapes, max_shapes
        self.min_cost_cover = min_cost_cover
        self.shape_learning = []
        self.reuse = reuse
        self.return_offers = return_offers
        self.reuse_pending = reuse_pending
        self.reuse_index = defaultdict(list)
        self.indexed_keys = 0
        self.reused_targets = 0
        self.local_filter = local_filter
        self.local_filter_rejections = 0
        self.blocked_cells = defaultdict(int)
        self.splits = {}
        self.levels = defaultdict(int)
        self.cells = list(root_cells())
        self.lazy_shapes = None
        self.lazy_ids = {}
        self.ratio_grid = [(Q(base**(i+1)), Q(base**i)) for i in range(bins)]
        self.float_ratio_grid = [tuple(map(fl, b)) for b in self.ratio_grid]
        names, ranges = (ib.STATES, ib.RANGES) if states == 6 else (ib.STATES13, ib.RANGES13)
        self.generic = defaultdict(list)
        self.imported_domains = defaultdict(list)
        if memory:
            shapes = {}
            for letters in product('123', repeat=memory):
                word = ''.join(letters)
                box = shape_image(word, (Q(F(1, 4)), Q(1)))
                for initial in ('', '3', '31', '313', '3131'):
                    if '31313' not in initial+word:
                        state = state_of(initial+word)
                        shapes.setdefault((state, box), initial+word)
            # A short fixed prefix containing 4 can have no all-123 memory
            # representative yet. Retain its exact initial shape as a domain.
            for root in self.cells:
                for state, box in zip(root.states, (root.r, root.s)):
                    shapes.setdefault((state, box), state)
            self.lazy_shapes = [(word, state, box, tuple(map(fl, box)))
                                for (state, box), word in shapes.items()]
        else:
            for s, t, p, h, qi in product(range(len(names)), range(len(names)), (1, -1),
                                         (False, True), range(bins)):
                cell = Cell((names[s], names[t]), p, h, tuple(map(Q, ranges[s])),
                            tuple(map(Q, ranges[t])), self.ratio_grid[qi])
                self.generic[tuple(map(state_of, cell.states)), p, h].append(len(self.cells))
                self.cells.append(cell)
        self.labels = set(map(tuple, labels))
        if self.shape_menu is not None:
            self.labels.update(z for shape in self.shape_menu for z in shape)
        self.labels.update(exchange(z) for z in tuple(self.labels))
        self.labels.update(('', a, '', b) for a, b in product((False, True), repeat=2))
        self.floatcells = []
        for c in self.cells:
            self.floatcells.append((tuple(map(fl, c.r)), tuple(map(fl, c.s)),
                                    tuple(map(fl, c.ratio)), tuple(map(fl, c.anchors()))))
        self.pool = lru_cache(None)(self._pool)
        self.points = lru_cache(None)(self.points)
        self.moves = lru_cache(None)(self._moves)
        self.ge = lru_cache(maxsize=500000)(self._ge)
        self.value = lru_cache(maxsize=500000)(self.value)
        self.outer_memberships = lru_cache(None)(self._outer_memberships)
        self.local_masks = lru_cache(None)(self._local_masks)
        self.native_geometry = lru_cache(maxsize=128)(self._native_geometry)
        self.shape_pairs = lru_cache(None)(self._shape_pairs)

    def _shape_pairs(self, states):
        if self.shape_menu is None:
            return ()
        lookup = {z[2]: i for i, z in enumerate(self.pool(states))}
        pairs = set()
        for shape in self.shape_menu:
            try:
                a, b = (lookup[endpoint(states, z)] for z in shape)
            except (ValueError, KeyError):
                continue
            if a != b:
                pairs.add(tuple(sorted((a, b))))
        return tuple(sorted(pairs))

    def generic_candidates(self, states, parity, high, r, s, ratio):
        if self.lazy_shapes is None:
            return self.generic[states, parity, high]
        chosen = []
        for state, image in zip(states, (r, s)):
            candidates = [i for i, (_, st, _, box) in enumerate(self.lazy_shapes)
                          if st == state and box[0] <= image[0]+2e-14 and image[1] <= box[1]+2e-14]
            if not candidates:
                return []
            chosen.append(min(candidates, key=lambda i: self.lazy_shapes[i][3][1]-self.lazy_shapes[i][3][0]))
        left, right = (self.lazy_shapes[i] for i in chosen)
        result = []
        for qi, qb in enumerate(self.float_ratio_grid):
            if max(qb[0], ratio[0]) > min(qb[1], ratio[1])+2e-14:
                continue
            key = (*chosen, parity, high, qi)
            if key not in self.lazy_ids:
                cell = Cell((left[0], right[0]), parity, high, left[2], right[2], self.ratio_grid[qi])
                self.lazy_ids[key] = len(self.cells)
                self.cells.append(cell)
                self.floatcells.append((left[3], right[3], qb, tuple(map(fl, cell.anchors()))))
            result.append(self.lazy_ids[key])
        return result

    def _local_masks(self, cid):
        """Necessary one-step support, using full child hulls optimistically.

        A real cover by truncated child intervals gives a chain of uniformly
        overlapping full hulls. Keep every such connected component; never
        infer filledness from this inexpensive precheck.
        """
        intervals = set()
        for move in self.moves(cid):
            mapped, order = move[5], move[7]
            intervals.add((mapped[order[0]], mapped[order[-1]]))
        intervals = list(intervals)
        parent = list(range(len(intervals)))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i

        for i, (a, b) in enumerate(intervals):
            for j, (c, d) in enumerate(intervals[:i]):
                if self.ge(cid, b, c) and self.ge(cid, d, a):
                    parent[find(i)] = find(j)
        lower, upper = [], []
        for point, _, _ in self.points(cid):
            low_mask = high_mask = 0
            for i, (a, b) in enumerate(intervals):
                if self.ge(cid, b, point):
                    high_mask |= 1 << find(i)
                    if self.ge(cid, point, a):
                        low_mask |= 1 << find(i)
            lower.append(low_mask)
            upper.append(high_mask)
        return lower, upper

    def locally_possible(self, key):
        if not self.local_filter:
            return True
        cid, lo, hi = key
        low_masks, high_masks = self.local_masks(cid)
        ok = bool(low_masks[lo] & high_masks[hi])
        if not ok:
            self.local_filter_rejections += 1
            self.blocked_cells[cid] += 1
        return ok

    def active_leaves(self, cid):
        if cid in self.splits:
            return [j for k in self.splits[cid] for j in self.active_leaves(k)]
        return [cid]

    def refine_boxes(self, count=12, max_depth=4):
        """Refine frequently blocking destination domains, then restart the game.

        Every split is a complete exact partition. Rejected types from the
        previous menu are deliberately not retained after the menu changes.
        """
        selected = sorted((i for i in self.blocked_cells if i >= 2 and
                           i not in self.splits and self.levels[i] < max_depth),
                          key=lambda i: (-self.blocked_cells[i], i))[:count]
        changed = []
        for cid in selected:
            cell = self.cells[cid]
            r, s, q, (a, b) = self.floatcells[cid]
            sizes = ((r[1]-r[0])/(1+a*sum(r)/2),
                     (s[1]-s[0])/(1+b*sum(s)/2), (q[1]-q[0])/(sum(q)/2))
            axis = max(range(3), key=lambda i: sizes[i])
            domains = [cell.r, cell.s, cell.ratio]
            lo, hi = domains[axis]
            if lo == hi:
                continue
            mid = (lo+hi)/2
            children = []
            for box in ((lo, mid), (mid, hi)):
                child_domains = list(domains)
                child_domains[axis] = box
                child = Cell(cell.states, cell.parity, cell.high, *child_domains)
                j = len(self.cells)
                self.cells.append(child)
                self.floatcells.append((tuple(map(fl, child.r)), tuple(map(fl, child.s)),
                                        tuple(map(fl, child.ratio)), tuple(map(fl, child.anchors()))))
                self.levels[j] = self.levels[cid]+1
                children.append(j)
            self.splits[cid] = children
            changed.append(dict(cell=cid, axis=('r', 's', 'ratio')[axis],
                                children=children, blocked=self.blocked_cells[cid]))
        self.moves.cache_clear()
        self.native_geometry.cache_clear()
        self.local_masks.cache_clear()
        self.reuse_index.clear()
        self.indexed_keys = 0
        self.blocked_cells.clear()
        self.failed_intervals.clear()
        return changed

    def grow_endpoint_menu(self, denominator):
        """Add O(N) boundary-grid endpoints; restart after point indices change."""
        before = len(self.labels)
        self.labels.update(edge_labels(denominator))
        self.pool.cache_clear()
        self.points.cache_clear()
        self.shape_pairs.cache_clear()
        self.moves.cache_clear()
        self.native_geometry.cache_clear()
        self.local_masks.cache_clear()
        self.outer_memberships.cache_clear()
        self.reuse_index.clear()
        self.indexed_keys = 0
        self.failed_intervals.clear()
        return dict(denominator=denominator, added_labels=len(self.labels)-before)

    def reuse_target(self, key, current):
        """Reuse an immutable containing type, with its entire domain unchanged."""
        if not self.reuse or self.game is None:
            return key
        game = self.game
        for new in game.keys[self.indexed_keys:]:
            self.reuse_index[new[0]].append(new)
        self.indexed_keys = len(game.keys)
        cid, low, high = key
        pool = self.points(cid)
        candidates = ([current] if current[0] == cid else [])
        candidates.extend(k for k in reversed(self.reuse_index[cid])
                          if game.entries[game.ids[k]]['status'] == 'local')
        if self.reuse_pending:
            candidates.extend(k for k in reversed(self.reuse_index[cid])
                              if game.entries[game.ids[k]]['status'] == 'pending')
        for old in candidates:
            if (self.ge(cid, pool[low][0], pool[old[1]][0])
                    and self.ge(cid, pool[old[2]][0], pool[high][0])):
                self.reused_targets += old != key
                return old
        return key

    def contains_type(self, outer, inner):
        if outer[0] != inner[0]:
            return False
        pool = self.points(outer[0])
        return self.ge(outer[0], pool[inner[1]][0], pool[outer[1]][0]) and self.ge(
            outer[0], pool[outer[2]][0], pool[inner[2]][0])

    def target_cost(self, key, current):
        if key == current:
            return 0
        entry = self.game.entries[self.game.ids[key]] if self.game is not None and key in self.game.ids else None
        if entry is not None and entry['status'] == 'local':
            return 0
        if self.reuse_pending and entry is None:
            return 2
        return 1

    def avoid_type(self, key):
        # Optional heuristic: failure in a finite menu does not establish
        # non-filledness. This pruning is never part of exact verification.
        if self.prune_supersets and any(self.contains_type(key, old) for old in self.failed_intervals[key[0]]):
            self.superset_rejections += 1
            return True
        return False

    def remember_failure(self, key):
        self.blocked_cells[key[0]] += 1
        if self.prune_supersets:
            old = self.failed_intervals[key[0]]
            if not any(self.contains_type(key, k) for k in old):
                self.failed_intervals[key[0]] = [k for k in old if not self.contains_type(k, key)]+[key]

    def _pool(self, states):
        points = {}
        for z in sorted(self.labels):
            try:
                xy = endpoint(states, z)
            except ValueError:
                continue
            points.setdefault(xy, z)
        return tuple((tuple(map(fl, xy)), label, xy) for xy, label in points.items())

    def points(self, cid):
        return self.pool(tuple(map(state_of, self.cells[cid].states)))

    def value(self, cid, point):
        r, s, q, (a, b) = self.floatcells[cid]
        r, s, q = (sum(z)/2 for z in (r, s, q))
        x, y = point
        return (1+r*a)**2*x/(1+r*x)+self.cells[cid].parity*q*(1+s*b)**2*y/(1+s*y)

    def parameter_samples(self, cid):
        rb, sb, qb, _ = self.floatcells[cid]
        middle = tuple(sum(z)/2 for z in (rb, sb, qb))
        samples = [middle]
        if self.outer_samples == 3:
            samples.extend((middle[0], middle[1], q) for q in qb)
        elif self.outer_samples == 9:
            samples.extend(product(rb, sb, qb))
        return samples

    def _outer_memberships(self, cid):
        """A finite outer approximation only REJECTS discovery candidates.

        No retained component is assumed filled. Using midpoint parameters
        here is a heuristic necessary-condition filter, never a proof gate.
        """
        cell = self.cells[cid]
        rb, sb, qb, anchors = self.floatcells[cid]
        signatures = [[] for _ in self.points(cid)]
        for r, s, q in self.parameter_samples(cid):
            def side_value(x, shape, a):
                return (1+shape*a)**2*x/(1+shape*x)
            sides = []
            for state, shape, a in zip(cell.states, (r, s), anchors):
                sides.append([(side_value(x, shape, a), side_value(y, shape, a))
                              for x, y in outer_tail_intervals(state_of(state), self.outer_depth)])
            right = sorted((a, b) if cell.parity > 0 else (-b, -a) for a, b in sides[1])
            intervals = []
            for lo, hi in sides[0]:
                low, high = lo+q*right[0][0], hi+q*right[0][1]
                for a, b in right[1:]:
                    if lo+q*a <= high+2e-13:
                        high = max(high, hi+q*b)
                    else:
                        intervals.append((low, high))
                        low, high = lo+q*a, hi+q*b
                intervals.append((low, high))
            merged = []
            for lo, hi in sorted(intervals):
                if merged and lo <= merged[-1][1]+2e-13:
                    merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
                else:
                    merged.append((lo, hi))
            for record, sig in zip(self.points(cid), signatures):
                x, y = record[0]
                z = side_value(x, r, anchors[0])+cell.parity*q*side_value(y, s, anchors[1])
                sig.append(next((i for i, (a, b) in enumerate(merged) if a-2e-13 <= z <= b+2e-13), -1))
        groups = {}
        return tuple(-1 if -1 in sig else groups.setdefault(tuple(sig), len(groups)) for sig in signatures)

    def outer_possible(self, key):
        if not self.outer_depth:
            return True
        cid, lo, hi = key
        ids = self.outer_memberships(cid)
        ok = ids[lo] >= 0 and ids[lo] == ids[hi]
        if not ok:
            self.outer_rejections += 1
            self.blocked_cells[cid] += 1
        return ok

    def _ge(self, cid, first, second):
        if first == second:
            return True
        rb, sb, qb, anchors = self.floatcells[cid]
        # All points are inside the hull, so each extremal anchor is on the
        # same side of both coordinates. The two endpoint evaluations suffice.
        ds = []
        for a, x, y, box in zip(anchors, first, second, (rb, sb)):
            values = [(x-y)*(1+a*r)**2/((1+x*r)*(1+y*r)) for r in box]
            ds.append((min(values), max(values)))
        dr = ds[1][0] if self.cells[cid].parity > 0 else -ds[1][1]
        return ds[0][0]+(qb[0] if dr >= 0 else qb[1])*dr >= -2e-14

    def image(self, cid, u, v, high):
        cell = self.cells[cid]
        states = tuple(state_of(s+w) for s, w in zip(cell.states, (u, v)))
        p = cell.parity*(-1)**(len(u)+len(v))
        rb, sb, qb, _ = self.floatcells[cid]
        new_anchors = (anchor(states[0], high), anchor(states[1], high if p > 0 else not high))
        factors, shapes = [], []
        for word, box, old, new in zip((u, v), (rb, sb), cell.anchors(), new_anchors):
            a, b, c, d = matrix(word)
            shapes.append(sorted((r*a+c)/(r*b+d) for r in box))
            if transform(word, new) == old:
                # A genuine periodic return must retain its exact multiplier.
                values = [fl(c*new+d)]*2
            else:
                old, new = fl(old), fl(new)
                values = [(r*(a*new+b)+c*new+d)/(1+r*old) for r in box]
            factors.append((min(values), max(values)))
        left, right = factors
        return (states, p, high, shapes[0], shapes[1],
                (qb[0]*(left[0]/right[1])**2, qb[1]*(left[1]/right[0])**2))

    def destinations(self, image):
        states, p, h, r, s, q = image
        # Prefer a special exact-ratio return domain when it contains the
        # whole image. Verification later checks these containments exactly.
        for j in (1, 0):
            c = self.cells[j]
            rb, sb, qb, _ = self.floatcells[j]
            if (states, p, h) == (c.states, c.parity, c.high) and all(
                    a[0] <= b[0]+2e-14 and b[1] <= a[1]+2e-14
                    for a, b in zip((rb, sb, qb), (r, s, q))):
                return [(j, False)]
        pieces = []
        if q[0] <= 1:
            pieces.append((states, h, r, s, (q[0], min(q[1], 1)), False))
        if q[1] > 1:
            pieces.append((states[::-1], h if p > 0 else not h, s, r,
                           (1/q[1], min(1/q[0], 1)), True))
        result = []
        for st, hh, rr, ss, qq, swap in pieces:
            # Reuse narrowed domains from an audited previous graph. Every
            # candidate covers the entire r/s image; sweep the full R image.
            # A hole falls back to the ordinary domain generator.
            known = []
            for j in self.imported_domains[st, p, hh]:
                rb, sb, qb, _ = self.floatcells[j]
                if all(a[0] <= b[0]+2e-14 and b[1] <= a[1]+2e-14
                       for a, b in zip((rb, sb), (rr, ss))):
                    known.append((qb, j))
            current, chosen = qq[0], []
            while current < qq[1]-2e-14 or not chosen:
                active = [(b, j) for b, j in known if b[0] <= current+2e-14
                          and b[1] >= current-2e-14
                          and (b[1] > current+2e-14 or qq[1]-qq[0] <= 2e-14)]
                if not active:
                    break
                box, j = max(active, key=lambda item: (item[0][1], -item[1]))
                chosen.append((j, swap))
                current = box[1]
                if current >= qq[1]-2e-14:
                    break
            if chosen and current >= qq[1]-2e-14:
                result.extend(chosen)
                continue
            matches = []
            for j in self.generic_candidates(st, p, hh, rr, ss, qq):
                rb, sb, qb, _ = self.floatcells[j]
                if not all(a[0] <= b[0]+2e-14 and b[1] <= a[1]+2e-14
                           for a, b in zip((rb, sb), (rr, ss))):
                    continue
                if max(qb[0], qq[0]) <= min(qb[1], qq[1])+2e-14:
                    matches.append((qb, j))
            current = qq[0]
            for (lo, hi), j in sorted(matches):
                if hi < current-2e-14:
                    continue
                # A zero-width boundary contact supplies no new part of a
                # nondegenerate image. Assign that shared boundary to the
                # advancing box, avoiding spurious ratio drift on returns.
                if qq[1]-qq[0] > 2e-14 and hi <= current+2e-14:
                    continue
                if lo > current+2e-14:
                    return None
                # Refining a destination box must retain all pieces meeting
                # the image, including closed boundary contacts.
                for leaf in self.active_leaves(j):
                    lr, ls, lq, _ = self.floatcells[leaf]
                    if all((max(a[0], b[0]) < min(a[1], b[1])-2e-14
                            if b[1]-b[0] > 2e-14 else
                            a[0] <= b[0]+2e-14 and b[1] <= a[1]+2e-14)
                           for a, b in zip((lr, ls, lq), (rr, ss, qq))):
                        result.append((leaf, swap))
                current = max(current, hi)
                if current >= qq[1]-2e-14:
                    break
            if current < qq[1]-2e-14 or not matches:
                return None
        return result or None

    def import_certificate(self, data, depth_first=False):
        """Resume obligations while preserving audited, immutable local rules.

        This restores a positive partial strategy, not historical failures.
        Missing endpoint labels must have been supplied to the constructor.
        """
        checker = Verifier(data)
        audit = checker.audit()
        if audit['failed_rules']:
            raise ValueError('cannot resume a graph with invalid local rules')
        lookup = {cell: i for i, cell in enumerate(self.cells)}
        cids = []
        for cell in checker.cells:
            cid = lookup.get(cell)
            if cid is None:
                cid = len(self.cells)
                lookup[cell] = cid
                self.cells.append(cell)
                self.floatcells.append((tuple(map(fl, cell.r)), tuple(map(fl, cell.s)),
                                        tuple(map(fl, cell.ratio)), tuple(map(fl, cell.anchors()))))
            cids.append(cid)
            signature = tuple(map(state_of, cell.states)), cell.parity, cell.high
            if cid not in self.imported_domains[signature]:
                self.imported_domains[signature].append(cid)
        keys = []
        for node in checker.nodes:
            cid = cids[node['cell']]
            points = {z[2]: i for i, z in enumerate(self.points(cid))}
            keys.append((cid, *(points[endpoint(self.cells[cid].states, node[k])]
                               for k in ('lower', 'upper'))))
        game = Game([keys[data['roots'][name]] for name in ('zero', 'positive')], depth_first)
        for key in keys:
            game.add(key)
        for node, key in zip(checker.nodes, keys):
            if not node.get('children'):
                continue
            plan = [dict(edge, destinations=[dict(key=keys[d['node']], swap=d['swap'])
                    for d in edge['destinations']]) for edge in node['children']]
            children = list(dict.fromkeys(game.ids[d['key']] for edge in plan for d in edge['destinations']))
            game.entries[game.ids[key]].update(status='local', plan=plan, children=children)
        for i, entry in enumerate(game.entries):
            for child in entry['children']:
                game.entries[child]['parents'].add(i)
        game.queue.clear()
        game.queued.clear()
        for i in sorted(game.reachable()):
            if game.entries[i]['status'] == 'pending':
                game.add(game.keys[i])
        self.game = game
        self.moves.cache_clear()
        self.native_geometry.cache_clear()
        self.local_masks.cache_clear()
        self.reuse_index.clear()
        self.indexed_keys = 0
        return game

    def child_candidates(self, cid, u, v, high):
        image = self.image(cid, u, v, high)
        return image, self.destinations(image)

    def child_routes(self, cid, u, v, high):
        """Alternative whole-domain routings for the same suffix pair."""
        yield self.child_candidates(cid, u, v, high)

    def _moves(self, cid):
        cell = self.cells[cid]
        states = tuple(map(state_of, cell.states))
        # Enumerate by the forbidden-word automaton, independently of the
        # optional suffix refinement in the generic parameter cells.
        suffixes = []
        for total in range(1, self.max_step+1):
            for i in range(total+1):
                for letters in product('123', repeat=total):
                    u, v = ''.join(letters[:i]), ''.join(letters[i:])
                    if '31313' not in states[0]+u and '31313' not in states[1]+v:
                        suffixes.append((u, v))
        periodic = []
        for s, h in zip(states, (cell.high, cell.high if cell.parity > 0 else not cell.high)):
            _, pre, period = extreme_tail(s, h)
            periodic.append((pre+period*3)[:6])
        suffixes.insert(0, tuple(periodic))
        suffixes.extend(self.macro_menu.get((states, cell.parity), ()))
        rb, sb, qb, (alpha, beta) = self.floatcells[cid]
        r, ss, q = (sum(z)/2 for z in (rb, sb, qb))
        def width(state, shape, a):
            x, y = fl(anchor(state, False)), fl(anchor(state, True))
            return (y-x)*(1+shape*a)**2/((1+shape*x)*(1+shape*y))
        left_width = width(states[0], r, alpha)
        right_width = q*width(states[1], ss, beta)
        moves = []
        for u, v in dict.fromkeys(suffixes):
            if not u+v or any('31313' in st+w or any(d not in '123' for d in w)
                              for st, w in zip(states, (u, v))):
                continue
            # Discovery policy: avoid repeatedly refining the much smaller
            # summand. Paired refinements and periodic returns remain allowed.
            if self.balance and ((not u and right_width < self.balance*left_width)
                                 or (not v and left_width < self.balance*right_width)):
                continue
            for high in (cell.high, not cell.high):
                for im, deps in self.child_routes(cid, u, v, high):
                    if not deps:
                        continue
                    pool = self.pool(im[0])
                    mapped = []
                    a, b, c, d = matrix(u)
                    aa, bb, cc, dd = matrix(v)
                    for (x, y), label, _ in pool:
                        mapped.append(((a*x+b)/(c*x+d), (aa*y+bb)/(cc*y+dd)))
                    mappings = []
                    for j, swap in deps:
                        lookup = {z[2]: k for k, z in enumerate(self.points(j))}
                        mappings.append(tuple(lookup[z[2][::-1] if swap else z[2]] for z in pool))
                    order = sorted(range(len(pool)), key=lambda k: self.value(cid, mapped[k]))
                    signatures = []
                    for k in range(len(pool)):
                        sig = tuple(self.outer_memberships(j)[ids[k]] for (j, _), ids in zip(deps, mappings)) if self.outer_depth else ()
                        signatures.append(None if -1 in sig else sig)
                    moves.append((u, v, high, deps, mappings, mapped, pool, order, signatures))
        return moves

    def planner(self, key, rejected):
        result = self._plan_once(key, rejected)
        if result is not None or not self.adaptive_shapes or self.shape_menu is None:
            return result
        if self.game is not None and key in self.game.permanent_rejections:
            return None
        # Only a failure triggers an unrestricted local probe. The probe does
        # not inherit negative conclusions from the smaller template menu.
        from learn_small_type_menu import shape_key
        previous, game = self.shape_menu, self.game
        known = {shape_key(s) for s in previous}
        if len(known) >= self.max_shapes:
            return None
        reuse_index, indexed_keys = self.reuse_index, self.indexed_keys
        self.reuse_index, self.indexed_keys = defaultdict(list), 0
        self.shape_menu = None
        self.native_geometry.cache_clear()
        self.game = Game([key])
        failed_intervals = self.failed_intervals
        self.failed_intervals = defaultdict(list)
        try:
            proposal = self._plan_once(key, self.game.rejected)
        finally:
            self.shape_menu, self.game = previous, game
            self.reuse_index, self.indexed_keys = reuse_index, indexed_keys
            self.failed_intervals = failed_intervals
            self.native_geometry.cache_clear()
        if proposal is None:
            return None
        added = sorted({shape_key((e['lower'], e['upper'])) for e in proposal[0]}-known)
        if not added or len(known)+len(added) > self.max_shapes:
            return None
        self.shape_menu = tuple(dict.fromkeys(previous+tuple(
            s for pair in added for s in (pair, tuple(exchange(z) for z in pair)))))
        self.shape_pairs.cache_clear()
        self.native_geometry.cache_clear()
        self.failed_intervals.clear()
        reopened = game.forget_rejections() if game is not None else 0
        self.shape_learning.append(dict(trigger=key, added=added, total=len(known)+len(added),
                                        reopened=reopened))
        return proposal

    def _plan_once(self, key, rejected):
        cid, low, high = key
        points = self.points(cid)
        start, end = points[low][0], points[high][0]
        if start == end or not self.ge(cid, end, start) or not self.outer_possible(key):
            # These filters depend on the fixed domain and endpoints, not
            # the current menu of child shapes. Enlarging that menu cannot
            # remove a gap already detected in the requested parent type.
            if self.game is not None:
                self.game.permanent_rejections.add(key)
            self.remember_failure(key)
            return None
        if self.avoid_type(key) or not self.locally_possible(key):
            self.remember_failure(key)
            return None
        if self.native_executable:
            return self.native_plan(key)
        # Search all retained contact alternatives; a failed farthest contact
        # is not treated as evidence that every cover fails.
        failed = set()

        def candidates(current, all_offers=False):
            offers = []
            current_value = self.value(cid, current)
            for u, v, h, deps, maps, mapped, pool, order, signatures in self.moves(cid):
                seen = set()

                def offer(lo, hi):
                    if (lo == hi or (lo, hi) in seen or signatures[lo] is None
                            or signatures[lo] != signatures[hi]
                            or self.value(cid, mapped[hi]) <= self.value(cid, mapped[lo])+1e-13
                            or (not all_offers and (self.value(cid, mapped[hi]) <= current_value+1e-13
                                or not self.ge(cid, current, mapped[lo])
                                or not self.ge(cid, mapped[hi], current)))
                            or not self.ge(cid, mapped[hi], mapped[lo])):
                        return False
                    keys = []
                    for (j, swap), ids in zip(deps, maps):
                        a, b = ids[lo], ids[hi]
                        dst = self.points(j)
                        if self.value(j, dst[a][0]) > self.value(j, dst[b][0]):
                            a, b = b, a
                        k = (j, a, b)
                        if (a == b or not self.outer_possible(k) or not self.locally_possible(k)
                                or not self.ge(j, dst[b][0], dst[a][0])):
                            return False
                        k = self.reuse_target(k, key)
                        if rejected(k) or self.avoid_type(k):
                            return False
                        keys.append(k)
                    edge = dict(suffixes=(u, v), high=h, lower=pool[lo][1], upper=pool[hi][1],
                                destinations=[dict(key=k, swap=swap) for k, (_, swap) in zip(keys, deps)])
                    cost = sum(self.target_cost(k, key) for k in set(keys)) if self.reuse else 0
                    offers.append((cost, self.value(cid, mapped[hi]), mapped[hi], edge, keys))
                    seen.add((lo, hi))
                    return True

                # A short known return may never occur among the farthest
                # `variants` endpoints. Generate it directly from known types.
                if self.return_offers and self.reuse and self.game is not None:
                    for (j, _), ids in zip(deps, maps):
                        inverse = {a: b for b, a in enumerate(ids)}
                        known = ([key] if key[0] == j else [])
                        known.extend(k for k, entry in zip(self.game.keys, self.game.entries)
                                     if k[0] == j and entry['status'] == 'local')
                        if self.reuse_pending:
                            known.extend(k for k, entry in zip(self.game.keys, self.game.entries)
                                         if k[0] == j and entry['status'] == 'pending')
                        for old in known:
                            lo, hi = inverse[old[1]], inverse[old[2]]
                            if self.value(cid, mapped[lo]) > self.value(cid, mapped[hi]):
                                lo, hi = hi, lo
                            offer(lo, hi)
                if self.shape_menu is not None:
                    states = tuple(state_of(st+w) for st, w in zip(self.cells[cid].states, (u, v)))
                    for lo, hi in self.shape_pairs(states):
                        if self.value(cid, mapped[lo]) > self.value(cid, mapped[hi]):
                            lo, hi = hi, lo
                        offer(lo, hi)
                    continue
                lowers = defaultdict(list)
                for k in reversed(order):
                    if signatures[k] is not None and self.ge(cid, current, mapped[k]):
                        lowers[signatures[k]].append(k)
                uppers = [k for k in reversed(order) if self.value(cid, mapped[k]) > current_value+1e-13
                          and signatures[k] in lowers and self.ge(cid, mapped[k], current)]
                count = 0
                for hi in uppers:
                    for lo in lowers[signatures[hi]]:
                        if (lo, hi) in seen or offer(lo, hi):
                            count += 1
                            break
                    if count >= self.variants:
                        break
            offers.sort(key=lambda z: (z[0], -z[1]))
            return offers

        if self.min_cost_cover and self.shape_menu is not None:
            # Endpoint contacts form a DAG: every edge strictly increases the
            # midpoint value, and uniform overlap is checked on the full cell.
            # Minimize additive (unproved-dependency cost, references, edges).
            offers = candidates(start, all_offers=True)
            records = []
            for cost, value, point, edge, keys in offers:
                lower = tuple(map(fl, endpoint(self.cells[cid].states, edge['lower'], edge['suffixes'])))
                records.append((lower, point, (cost, len(set(keys)), 1)))
            selected = minimum_cover_chain(records, start, end, lambda a, b: self.ge(cid, a, b),
                                           lambda point: self.value(cid, point))
            if selected is not None:
                chain = [offers[i] for i in selected]
                return [z[3] for z in chain], [k for z in chain for k in z[4]]
            self.remember_failure(key)
            return None

        # Explicit DFS avoids recursion limits when a cover has many contacts.
        stack = [(start, None)]
        path = []
        while stack:
            current, it = stack[-1]
            if self.ge(cid, current, end):
                return ([e for e, _ in path], [k for _, ks in path for k in ks])
            if it is None:
                it = iter(candidates(current))
                stack[-1] = (current, it)
            for _, _, nxt, edge, keys in it:
                if nxt not in failed:
                    path.append((edge, keys))
                    stack.append((nxt, None))
                    break
            else:
                failed.add(current)
                stack.pop()
                if path:
                    path.pop()
        self.remember_failure(key)
        return None

    def native_cell(self, cid):
        r, s, q, anchors = self.floatcells[cid]
        return (self.cells[cid].parity, *r, *s, *q, *anchors)

    def native_point(self, cid, point):
        return point

    def _native_geometry(self, cid):
        moves = self.moves(cid)
        cids = {cid} | {j for move in moves for j, _ in move[3]}
        lines = []
        def line(values):
            lines.append(' '.join(map(str, values)))
        for j in sorted(cids):
            cell = self.cells[j]
            r, s, q, anchors = self.floatcells[j]
            pool = self.points(j)
            line((j, *self.native_cell(j), len(pool)))
            line(x for record in pool for x in self.native_point(j, record[0]))
        cell_text = '\n'.join(lines)+'\n'
        lines = []
        for move in moves:
            u, v, _, deps, maps, mapped, pool, order, signatures = move
            groups = {}
            line((len(mapped), len(deps)))
            line(x for point in mapped for x in self.native_point(cid, point))
            line(order)
            line(-1 if sig is None else groups.setdefault(sig, len(groups)) for sig in signatures)
            for (j, _), ids in zip(deps, maps):
                line((j, *ids))
            states = tuple(state_of(st+w) for st, w in zip(self.cells[cid].states, (u, v)))
            pairs = self.shape_pairs(states)
            line((len(pairs), *(k for pair in pairs for k in pair)))
        return cids, cell_text, '\n'.join(lines)+'\n'

    def native_plan(self, key):
        """Accelerate floating contact search; certificate semantics are unchanged."""
        moves = self.moves(key[0])
        cids, cell_text, move_text = self.native_geometry(key[0])
        lines = [' '.join(map(str, (len(cids), len(moves), self.variants, int(self.reuse),
                                    int(self.return_offers), int(self.shape_menu is not None),
                                    int(self.min_cost_cover), *key)))+'\n', cell_text]
        for status in ('rejected', 'local'):
            keys = [k for k, entry in zip(self.game.keys, self.game.entries)
                    if k[0] in cids and entry['status'] == status]
            lines.append(str(len(keys))+'\n')
            lines.extend(' '.join(map(str, k))+'\n' for k in keys)
        keys = [k for k, entry in zip(self.game.keys, self.game.entries)
                if k[0] in cids and entry['status'] == 'pending'] if self.reuse_pending else []
        lines.append(str(int(self.reuse_pending))+' '+str(len(keys))+'\n')
        lines.extend(' '.join(map(str, k))+'\n' for k in keys)
        failed = [k for cid in cids for k in self.failed_intervals[cid]] if self.prune_supersets else []
        lines.append(str(len(failed))+'\n')
        lines.extend(' '.join(map(str, k))+'\n' for k in failed)
        lines.append(move_text)
        if self.native_process is None:
            self.native_process = subprocess.Popen([str(self.native_executable)],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, bufsize=1)
        process = self.native_process
        process.stdin.write(''.join(lines))
        process.stdin.flush()
        reply = process.stdout.readline()
        if not reply:
            raise RuntimeError('native planner exited: '+process.stderr.read())
        result = json.loads(reply)
        self.reused_targets += result['reused']
        self.superset_rejections += result['pruned']
        if not result['found']:
            self.remember_failure(key)
            return None
        edges, all_keys = [], []
        for item in result['offers']:
            u, v, high, deps, _, _, pool, _, _ = moves[item['move']]
            keys = list(map(tuple, item['keys']))
            edges.append(dict(suffixes=(u, v), high=high, lower=pool[item['lo']][1],
                              upper=pool[item['hi']][1], destinations=[dict(key=k, swap=swap)
                                for k, (_, swap) in zip(keys, deps)]))
            all_keys.extend(keys)
        return edges, all_keys

    def close_native(self):
        if self.native_process is not None:
            process = self.native_process
            try:
                process.stdin.close()
            except BrokenPipeError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.terminate()
                process.wait(timeout=5)
            process.stdout.close()
            process.stderr.close()
            self.native_process = None

    def roots(self):
        roots = []
        for cid in (0, 1):
            labels = full_labels(self.cells[cid].parity)
            lookup = {z[2]: i for i, z in enumerate(self.points(cid))}
            roots.append((cid, *(lookup[endpoint(self.cells[cid].states, z)] for z in labels)))
        return roots

    def certificate(self, game):
        reached = sorted(game.reachable())
        ids = {j: i for i, j in enumerate(reached)}
        used = sorted({game.keys[j][0] for j in reached})
        cell_ids = {j: i for i, j in enumerate(used)}
        nodes = []
        for j in reached:
            cid, lo, hi = game.keys[j]
            entry = game.entries[j]
            labels = (self.points(cid)[lo][1], self.points(cid)[hi][1])
            if self.shape_menu is not None:
                from learn_small_type_menu import template_labels
                labels = template_labels(self.cells[cid].states, self.points(cid)[lo][2],
                                         self.points(cid)[hi][2], self.shape_menu)
            row = dict(cell=cell_ids[cid], lower=labels[0], upper=labels[1], children=[])
            if entry['status'] == 'local':
                for edge in entry['plan']:
                    row['children'].append(dict(edge, destinations=[
                        dict(node=ids[game.ids[d['key']]], swap=d['swap']) for d in edge['destinations']]))
            nodes.append(row)
        return dict(format='freiman-cyclic-types-v1', cells=[self.cells[i].record() for i in used],
                    nodes=nodes, roots=dict(zip(('zero', 'positive'), (ids[i] for i in game.roots))),
                    search=game.summary())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--endpoints', type=Path, default=Path(__file__).with_name('adaptive_depth8_certificate.json'))
    parser.add_argument('--macro-menu', type=Path, help='learned composed successors; re-evaluated on the parent domain')
    parser.add_argument('--shape-menu', type=Path, help='restrict new interval shapes to this small menu')
    parser.add_argument('--adaptive-shapes', action='store_true',
                        help='add shapes from an unrestricted local cover only when the small menu fails')
    parser.add_argument('--max-shapes', type=int, default=64)
    parser.add_argument('--min-cost-cover', action='store_true',
                        help='optimize the entire cover chain over the small template menu')
    parser.add_argument('--states', type=int, choices=(6, 13), default=6)
    parser.add_argument('--memory', type=int, default=0,
                        help='lazily create domains from this many final digits (0 uses --states)')
    parser.add_argument('--bins', type=int, default=25)
    parser.add_argument('--base', type=F, default=F(22, 25))
    parser.add_argument('--max-step', type=int, default=2)
    parser.add_argument('--variants', type=int, default=4)
    parser.add_argument('--outer-depth', type=int, default=3)
    parser.add_argument('--outer-samples', type=int, choices=(1, 3, 9), default=3)
    parser.add_argument('--grid', type=int, default=0,
                        help='add interpolated tail-hull endpoints with this denominator')
    parser.add_argument('--edge-grid', type=int, default=0)
    parser.add_argument('--grow-edge-grid', action='store_true',
                        help='double the boundary endpoint grid between refinement rounds')
    parser.add_argument('--no-reuse', action='store_true')
    parser.add_argument('--no-return-offers', action='store_true',
                        help='disable direct offers from known types (comparison only)')
    parser.add_argument('--reuse-pending', action='store_true',
                        help='reuse containing unresolved types; all remain proof obligations')
    parser.add_argument('--breadth-first', action='store_true')
    parser.add_argument('--no-local-filter', action='store_true')
    parser.add_argument('--prune-supersets', action='store_true',
                        help='heuristically avoid intervals containing failed obligations')
    parser.add_argument('--balance', type=F, default=F(0),
                        help='only refine one side if its midpoint width is at least this times the other')
    parser.add_argument('--native-executable', type=Path,
                        help='optional compiled cyclic_planner.cpp; use with --no-local-filter')
    parser.add_argument('--refinement-rounds', type=int, default=1)
    parser.add_argument('--split-count', type=int, default=12)
    parser.add_argument('--split-depth', type=int, default=4)
    parser.add_argument('--max-types', type=int, default=10000)
    parser.add_argument('--max-steps', type=int, default=100000)
    parser.add_argument('--seconds', type=float, default=600)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not (0 < args.base < 1 and args.bins > 0 and args.max_step > 0 and args.variants > 0
            and args.outer_depth >= 0 and args.grid >= 0 and args.max_types >= 2
            and args.max_steps > 0 and args.seconds > 0 and args.refinement_rounds > 0
            and args.split_count > 0 and args.split_depth > 0 and args.memory >= 0
            and args.edge_grid >= 0 and args.balance >= 0 and args.max_shapes >= 2):
        parser.error('positive search bounds, base in (0,1), and nonnegative grid depths are required')
    data = json.loads(args.endpoints.read_text())
    shapes = data.get('types', [])
    for case in data.get('cases', []):
        shapes.extend(case['types'])
    labels = [z for shape in shapes for z in shape]
    if args.grid > 0:
        labels.extend((f'@{F(i, args.grid)}', False, f'@{F(j, args.grid)}', False)
                      for i, j in product(range(args.grid+1), repeat=2))
    labels.extend(edge_labels(args.edge_grid))
    macro_menu = {}
    if args.macro_menu:
        for row in json.loads(args.macro_menu.read_text())['macros']:
            macro_menu[tuple(row['states']), row['parity']] = [tuple(z['suffixes']) for z in row['successors']]
    shape_menu = None if args.shape_menu is None else [row['endpoints']
                  for row in json.loads(args.shape_menu.read_text())['shapes']]
    if args.adaptive_shapes and shape_menu is None:
        shape_menu = [full_labels(1), full_labels(-1)]
    search = Search(labels, args.states, args.bins,
                    args.base, args.max_step, args.variants, args.outer_depth, not args.no_reuse,
                    not args.no_local_filter, args.outer_samples, args.memory, args.prune_supersets,
                    args.balance, not args.no_return_offers, args.reuse_pending, macro_menu, shape_menu,
                    args.adaptive_shapes, args.max_shapes, args.min_cost_cover)
    if args.native_executable:
        if not args.no_local_filter:
            parser.error('--native-executable requires --no-local-filter')
        search.native_executable = args.native_executable.resolve()
    game = Game(search.roots(), depth_first=not args.breadth_first)
    search.game = game
    refinement_history = []

    def checkpoint(game):
        cert = search.certificate(game)
        cert['settings'] = {k: str(v) if isinstance(v, (Path, F)) else v for k, v in vars(args).items()}
        cert['search']['outer_filter_rejections'] = search.outer_rejections
        cert['search']['reused_targets'] = search.reused_targets
        cert['search']['local_filter_rejections'] = search.local_filter_rejections
        cert['search']['superset_rejections'] = search.superset_rejections
        cert['search']['closed_supported_types'] = len(game.supported())
        cert['refinement_history'] = refinement_history
        cert['shape_learning'] = search.shape_learning
        cert['shape_menu'] = search.shape_menu
        temporary = args.output.with_suffix(args.output.suffix+'.tmp')
        temporary.write_text(json.dumps(cert, indent=2)+'\n')
        temporary.replace(args.output)
        print(json.dumps(game.summary()), flush=True)

    deadline = time.monotonic()+args.seconds
    try:
        for iteration in range(args.refinement_rounds):
            game = Game(search.roots(), depth_first=not args.breadth_first)
            search.game = game
            checkpoint(game)
            remaining = deadline-time.monotonic()
            if remaining <= 0:
                game.stop = 'time limit'
                break
            game.run(search.planner, args.max_types, args.max_steps,
                     remaining/(args.refinement_rounds-iteration), checkpoint)
            stage = dict(round=iteration, search=game.summary(), cells=len(search.cells))
            refinement_history.append(stage)
            checkpoint(game)
            stage_path = args.output.with_suffix(f'.round-{iteration}.json')
            stage_path.write_text(args.output.read_text())
            if game.closed():
                break
            if iteration+1 < args.refinement_rounds:
                stage['splits'] = search.refine_boxes(args.split_count, args.split_depth)
                if args.grow_edge_grid:
                    stage['endpoint_refinement'] = search.grow_endpoint_menu(max(4, args.edge_grid)*2**(iteration+1))
                if not stage['splits'] and not args.grow_edge_grid:
                    break
    except KeyboardInterrupt:
        game.stop = 'interrupted; unresolved obligations retained'
    finally:
        search.close_native()
    checkpoint(game)
    if game.closed():
        result = Verifier(search.certificate(game)).closed()
        args.output.with_suffix('.verified.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
