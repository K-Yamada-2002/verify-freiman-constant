"""Lazy finite AND/OR search, with immutable types and parent repair.

The planner proposes (payload, child keys), avoiding rejected keys. Cycles are
allowed. Only a complete reachable graph counts as a candidate, and geometry
must still be replayed independently. Resource limits never reject a type.
"""
from collections import deque
import copy
import time


class Game:
    def __init__(self, roots, depth_first=True):
        self.depth_first = depth_first
        self.keys, self.ids, self.entries = [], {}, []
        self.queue, self.queued = deque(), set()
        self.steps = self.repairs = 0
        self.permanent_rejections = set()
        self.roots = [self.add(k) for k in roots]
        self.stop = 'not started'

    def add(self, key, urgent=False):
        if key not in self.ids:
            self.ids[key] = len(self.keys)
            self.keys.append(key)
            self.entries.append(dict(status='pending', plan=None, children=[], parents=set()))
        i = self.ids[key]
        if self.entries[i]['status'] == 'pending' and i not in self.queued:
            if self.depth_first or urgent:
                self.queue.appendleft(i)
            else:
                self.queue.append(i)
            self.queued.add(i)
        return i

    def rejected(self, key):
        i = self.ids.get(key)
        return i is not None and self.entries[i]['status'] == 'rejected'

    def reject(self, key, permanent=False):
        """Invalidate one known obligation and schedule its incoming repairs."""
        i = self.ids[key]
        if permanent:
            self.permanent_rejections.add(key)
        entry = self.entries[i]
        for child in entry['children']:
            self.entries[child]['parents'].discard(i)
        entry.update(status='rejected', plan=None, children=[])
        if i in self.queued:
            self.queue.remove(i)
            self.queued.remove(i)
        for parent in tuple(entry['parents']):
            if self.entries[parent]['status'] != 'rejected':
                self.entries[parent]['status'] = 'pending'
                self.add(self.keys[parent], urgent=True)
                self.repairs += 1

    def forget_rejections(self):
        """A larger candidate menu invalidates negative discovery decisions.

        Existing positive rules keep the same types and geometric meaning.
        Reopen old failures; their parent repairs are already pending.
        """
        reopened = 0
        for i, entry in enumerate(self.entries):
            if entry['status'] == 'rejected' and self.keys[i] not in self.permanent_rejections:
                entry['status'] = 'pending'
                self.add(self.keys[i])
                reopened += 1
        return reopened

    def reachable(self):
        reached, todo = set(), list(self.roots)
        while todo:
            i = todo.pop()
            if i in reached:
                continue
            reached.add(i)
            # A pending parent's old plan is invalid. Its former descendants
            # become obligations again only if the replacement plan uses them.
            if self.entries[i]['status'] == 'local':
                todo.extend(self.entries[i]['children'])
        return reached

    def closed(self):
        return bool(self.roots) and all(self.entries[i]['status'] == 'local' for i in self.reachable())

    def run(self, planner, max_types=10000, max_steps=100000, seconds=600, checkpoint=None):
        deadline = time.monotonic()+seconds
        self.stop = 'pending'
        while self.queue and self.steps < max_steps:
            if time.monotonic() >= deadline:
                self.stop = 'time limit'
                break
            i = self.queue.popleft()
            self.queued.remove(i)
            entry = self.entries[i]
            proposal = planner(self.keys[i], self.rejected)
            self.steps += 1
            for j in entry['children']:
                self.entries[j]['parents'].discard(i)
            entry.update(status='pending', children=[], plan=None)
            if proposal is None:
                entry['status'] = 'rejected'
                for parent in tuple(entry['parents']):
                    if self.entries[parent]['status'] != 'rejected':
                        self.entries[parent]['status'] = 'pending'
                        self.add(self.keys[parent], urgent=True)
                        self.repairs += 1
                if any(self.entries[r]['status'] == 'rejected' for r in self.roots):
                    self.stop = 'root rejected in this candidate menu'
                    break
            else:
                plan, keys = proposal
                if len(self.keys)+len(set(keys)-self.ids.keys()) > max_types:
                    self.stop = 'type limit'
                    self.add(self.keys[i])
                    break
                # Mark the parent before add(): a self-loop is an already
                # solved local rule, not fresh work to push ahead of its siblings.
                entry['status'] = 'local'
                children = list(dict.fromkeys(self.add(k) for k in keys))
                entry.update(status='local', children=children, plan=plan)
                for j in children:
                    self.entries[j]['parents'].add(i)
            if self.steps % 64 == 0 or not self.queue:
                if self.closed():
                    self.stop = 'closed candidate'
                    break
                active = self.reachable()
                self.queue = deque(j for j in self.queue if j in active)
                self.queued = set(self.queue)
                for j in sorted(active):
                    if self.entries[j]['status'] == 'pending':
                        self.add(self.keys[j])
            if checkpoint and self.steps % 100 == 0:
                checkpoint(self)
        if self.closed():
            self.stop = 'closed candidate'
        elif self.steps >= max_steps:
            self.stop = 'step limit'
        return self

    def summary(self):
        reached = self.reachable()
        return dict(registered=len(self.keys), reachable=len(reached),
                    unresolved=sum(self.entries[i]['status'] != 'local' for i in reached),
                    rejected=sum(e['status'] == 'rejected' for e in self.entries),
                    steps=self.steps, parent_repairs=self.repairs, stop=self.stop,
                    closed_candidate=self.closed())

    def supported(self):
        """Greatest closed subset of the currently chosen local rules."""
        alive = {i for i, e in enumerate(self.entries) if e['status'] == 'local'}
        failed = deque(set(range(len(self.entries)))-alive)
        while failed:
            i = failed.popleft()
            for parent in self.entries[i]['parents']:
                if parent in alive:
                    alive.remove(parent)
                    failed.append(parent)
        return alive

    def snapshot(self):
        """Search state, including failures and queue order; not a proof."""
        return dict(format='finite-type-game-state-v1', depth_first=self.depth_first,
                    keys=copy.deepcopy(self.keys), roots=self.roots[:], queue=list(self.queue),
                    entries=[{k: copy.deepcopy(e[k]) for k in ('status', 'plan', 'children')} for e in self.entries],
                    steps=self.steps, repairs=self.repairs, stop=self.stop,
                    permanent_rejections=list(self.permanent_rejections))

    @classmethod
    def restore(cls, data):
        def freeze(x):
            return tuple(freeze(z) for z in x) if isinstance(x, (tuple, list)) else x
        def restore_plan(x):
            if isinstance(x, dict):
                return {k: freeze(v) if k == 'key' else restore_plan(v) for k,v in x.items()}
            if isinstance(x, (tuple, list)):
                return [restore_plan(z) for z in x]
            return x
        if data['format'] != 'finite-type-game-state-v1':
            raise ValueError('unknown search state')
        game = cls([], data['depth_first'])
        game.keys = [freeze(k) for k in data['keys']]
        game.ids = {k: i for i,k in enumerate(game.keys)}
        if len(game.ids) != len(game.keys) or len(data['entries']) != len(game.keys):
            raise ValueError('duplicate keys or mismatched entries')
        game.entries = []
        for entry in data['entries']:
            if entry['status'] not in ('local', 'pending', 'rejected'):
                raise ValueError('unknown obligation status')
            game.entries.append(dict(status=entry['status'], plan=restore_plan(entry['plan']),
                                     children=list(entry['children']), parents=set()))
        n = len(game.keys)
        def valid_index(i):
            return type(i) is int and 0 <= i < n
        game.roots = list(data['roots'])
        game.queue = deque(data['queue'])
        game.queued = set(game.queue)
        if len(game.queued) != len(game.queue) or not all(valid_index(i) for i in game.roots+list(game.queue)):
            raise ValueError('invalid roots or queue')
        for i, entry in enumerate(game.entries):
            for j in entry['children']:
                if not valid_index(j):
                    raise ValueError('invalid dependency index')
                game.entries[j]['parents'].add(i)
        game.permanent_rejections = {freeze(k) for k in data['permanent_rejections']}
        if not game.permanent_rejections <= game.ids.keys():
            raise ValueError('unknown permanent rejection')
        game.steps, game.repairs, game.stop = data['steps'], data['repairs'], data['stop']
        if type(game.steps) is not int or type(game.repairs) is not int or min(game.steps, game.repairs) < 0:
            raise ValueError('invalid search counters')
        return game
