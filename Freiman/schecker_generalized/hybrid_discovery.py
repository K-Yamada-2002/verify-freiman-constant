"""Productive discovery lanes for the fair certificate search.

Neither lane decides nonexistence. Mosaic searches all endpoint paths in its
fixed offer catalog, transferring offers to a new domain only after an exact
child check. Constructive search keeps failed obligations open and synthesizes
proper-digit rules and new child types. Only the separate verifier certifies.
"""
from collections import defaultdict, deque
import copy
import json

from chart_geometry import compare
from contract_piecewise_charts import edges, rules
from finite_type_game import Game
from search_piecewise_charts import fingerprint, restore
from type_graph_geometry import endpoint
from verify_piecewise_charts import PiecewiseVerifier


def signature(domain):
    return domain.states, domain.parity, domain.high


class Mosaic:
    """Resumable lazy BFS; one catalog edge per step, no candidate/beam cap.

Only existing types are referenced, so adding a rule to an open node cannot
enlarge the reachable universe of an initially reachable source graph. Rules
may combine individual edges from different source recipes and guard pieces.
"""
    def __init__(self, graph=None, state=None):
        self.graph = copy.deepcopy(graph if state is None else state['graph'])
        self.checker = PiecewiseVerifier(self.graph)
        audit = self.checker.audit()
        if audit['failed_rules']:
            raise ValueError('invalid mosaic input')
        if state is None:
            groups, catalog, seen = defaultdict(list), [], {}
            incoming = defaultdict(int)
            for node in self.checker.nodes:
                for edge in edges(node):
                    for dest in edge['destinations']:
                        incoming[dest['node']] += 1
                for rule in rules(node):
                    sig = signature(self.checker.cells[rule['cell']])
                    for edge in rule['children']:
                        encoded = sig, json.dumps(edge, sort_keys=True, separators=(',', ':'))
                        if encoded not in seen:
                            seen[encoded] = len(catalog)
                            catalog.append(dict(cell=rule['cell'], edge=copy.deepcopy(edge)))
                            groups[sig].append(len(catalog)-1)
            self.catalog = catalog
            self.targets = sorted(audit['open_nodes'], key=lambda i: (-incoming[i], i))
            self.position, self.work = 0, None
            self.statistics = dict(edge_trials=0, child_checks=0, child_failures=0,
                                   cache_hits=0, accepted=0, exhausted_targets=0)
            self.cache = {}
        else:
            self.catalog = copy.deepcopy(state['catalog'])
            self.targets = list(state['targets'])
            self.position = state['position']
            self.work = copy.deepcopy(state['work'])
            self.statistics = dict(state['statistics'])
            self.cache = {(cid, offer): success for cid, offer, success in state['cache']}
        self.groups = defaultdict(list)
        self.ends = {}
        for i, row in enumerate(self.catalog):
            domain = self.checker.cells[row['cell']]
            self.groups[signature(domain)].append(i)
            self.ends[i] = tuple(endpoint(domain.states, row['edge'][k], row['edge']['suffixes'])
                                 for k in ('lower', 'upper'))

    @property
    def finished(self):
        return self.position >= len(self.targets)

    def snapshot(self):
        return dict(graph=self.graph, catalog=self.catalog, targets=self.targets,
                    position=self.position, work=self.work, statistics=self.statistics,
                    cache=[[cid, offer, ok] for (cid, offer), ok in sorted(self.cache.items())])

    def step(self):
        if self.finished:
            return False
        i = self.targets[self.position]
        node, domain, low, high = self.checker.node(i)
        options = self.groups[signature(domain)]
        if self.work is None:
            # -1 is the initial endpoint; other endpoint IDs are catalog IDs.
            self.work = dict(frontier=[-1], current=0, edge=0, previous={})
        work = self.work
        if work['current'] >= len(work['frontier']):
            self.statistics['exhausted_targets'] += 1
            self.position += 1
            self.work = None
            return True
        if work['edge'] >= len(options):
            work['current'] += 1
            work['edge'] = 0
            return True
        offer_id = options[work['edge']]
        at = work['frontier'][work['current']]
        current = low if at == -1 else self.ends[at][1]
        a, b = self.ends[offer_id]
        reached = {low} | {self.ends[j][1] for j in work['frontier'] if j != -1}
        # Child geometry is expensive. First check exact contacts at an
        # endpoint already reached; do not test unreachable offers eagerly.
        usable = b not in reached and compare(domain, current, a) and compare(domain, b, current, strict=True)
        edge = self.catalog[offer_id]['edge']
        if usable:
            cache_key = node['cell'], offer_id
            if cache_key not in self.cache:
                self.statistics['child_checks'] += 1
                try:
                    self.checker.child(domain, edge)
                except ValueError:
                    self.statistics['child_failures'] += 1
                    self.cache[cache_key] = False
                else:
                    self.cache[cache_key] = True
            else:
                self.statistics['cache_hits'] += 1
            usable = self.cache[cache_key]
        if usable and compare(domain, b, high):
            path, previous = [offer_id], at
            while previous != -1:
                path.append(previous)
                previous = work['previous'][str(previous)]
            proposal = [copy.deepcopy(self.catalog[j]['edge']) for j in reversed(path)]
            old = copy.deepcopy(node)
            node['children'] = proposal
            self.checker.checked.pop(i, None)
            try:
                self.checker.local(i)
            except BaseException:
                self.checker.nodes[i] = old
                self.checker.checked.pop(i, None)
                raise
            self.statistics['accepted'] += 1
            self.position += 1
            self.work = None
        else:
            if usable:
                work['previous'][str(offer_id)] = at
                work['frontier'].append(offer_id)
            work['edge'] += 1
        self.statistics['edge_trials'] += 1
        return True


class Constructive:
    """Continue synthesis without making local rules invalidate their parents.

Each successful proposal is checked on an isolated probe before registration.
Finite-menu failures remain pending obligations; after one whole sweep the
discovery bounds grow and negative caches are reset. This lane is heuristic.
"""
    def __init__(self, seed=None, state=None):
        self.search, self.game, self.config = restore(seed if state is None else state['search'])
        if state is None:
            # This lane starts a new policy. Old heuristic rejections are not
            # mathematical obstructions and must not survive that change.
            self.game.permanent_rejections.clear()
            self.game.forget_rejections()
            self.search.failed_intervals.clear()
            self.round = 0
            self.statistics = dict(attempts=0, accepted=0, no_rule=0, exact_rejected=0, sweeps=0)
            self.todo = deque()
            self.queued = set()
            self.attempted = set()
            self.enqueue_open()
        else:
            self.round = state['round']
            self.statistics = dict(state['statistics'])
            self.todo = deque(state['todo'])
            self.queued = set(self.todo)
            self.attempted = set(state['attempted'])

    def enqueue_open(self):
        active = self.game.reachable()
        for i in sorted(active, key=lambda j: (-len(self.game.entries[j]['parents']), j)):
            if self.game.entries[i]['status'] != 'local' and i not in self.queued and i not in self.attempted:
                self.todo.append(i)
                self.queued.add(i)

    def widen(self):
        self.round += 1
        self.statistics['sweeps'] += 1
        self.config['max_shapes'] += 8
        if self.round % 2:
            self.config['partition_depth'] += 1
        else:
            self.config['max_step'] += 1
        # Reconstruct rather than keep stale cached moves/negative results
        # after changing the generation language. Positive rules are retained.
        saved = self.search.snapshot(self.game, self.config, fingerprint())
        saved['engine_hash'] = 'hybrid discovery menu expanded'
        self.search.close_native()
        self.search, self.game, self.config = restore(saved)
        self.attempted.clear()
        self.enqueue_open()

    def step(self):
        if self.game.closed():
            return False
        if not self.todo:
            self.widen()
            return True
        i = self.todo[0]
        entry = self.game.entries[i]
        if entry['status'] == 'local':
            self.todo.popleft()
            self.queued.remove(i)
            return True
        key = self.game.keys[i]
        proposal = self.search.planner(key, lambda unused: False)
        if proposal is not None:
            plan, children = proposal
            probe = Game([key])
            for child in children:
                probe.add(child)
            probe.entries[0].update(status='local', plan=plan,
                                    children=[probe.ids[k] for k in children])
            try:
                PiecewiseVerifier(self.search.certificate(probe)).local(0)
            except ValueError:
                self.statistics['exact_rejected'] += 1
                proposal = None
        # A failed planner never deletes an obligation or an existing rule.
        if proposal is not None:
            entry['status'] = 'local'
            ids = list(dict.fromkeys(self.game.add(k) for k in children))
            entry.update(plan=copy.deepcopy(plan), children=ids)
            for j in ids:
                self.game.entries[j]['parents'].add(i)
            self.statistics['accepted'] += 1
        else:
            self.statistics['no_rule'] += 1
        self.statistics['attempts'] += 1
        self.game.steps += 1
        self.attempted.add(i)
        self.todo.popleft()
        self.queued.remove(i)
        self.enqueue_open()
        return True

    def snapshot(self):
        return dict(search=self.search.snapshot(self.game, self.config, fingerprint()),
                    todo=list(self.todo), attempted=sorted(self.attempted), round=self.round,
                    statistics=self.statistics)

    def graph(self):
        return self.search.certificate(self.game)
