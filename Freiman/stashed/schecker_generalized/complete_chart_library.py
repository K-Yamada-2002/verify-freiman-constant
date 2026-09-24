"""Exact AND/OR closure over a precisely specified finite chart library.

For each EXACT parameter domain, retain all saved offered intervals and all
saved guard layouts. Arbitrary chains of those offers, and arbitrary subsets
of their saved destination references, are allowed. There is no float filter,
beam, greedy endpoint ordering, or limit on the number of rule alternatives.
This finite-menu completeness does not cover words/domains absent from the
library; the independent exhaustive stream handles that larger guarantee.
"""
from collections import defaultdict, deque
import copy
import hashlib
import json

from chart_geometry import compare
from contract_piecewise_charts import prune, rules
from type_graph_geometry import endpoint
from verify_piecewise_charts import FORMAT, PiecewiseVerifier


def digest(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


class FiniteClosure:
    """Greatest fixed point for a monotone, exhaustive finite-rule oracle.

oracle(i, alive) returns a payload and ALL its dependencies, or None iff no
rule for i uses only alive types. A failed chosen rule triggers a fresh full
query, so mutually supporting cycles and alternative strategies are retained.
"""
    def __init__(self, size, oracle, state=None):
        self.size, self.oracle = size, oracle
        self.dirty = False
        if state is None:
            self.alive = set(range(size))
            self.queue = deque(range(size))
            self.plans, self.removed, self.steps = {}, [], 0
        else:
            if state['size'] != size:
                raise ValueError('changed finite universe')
            self.alive = set(state['alive'])
            self.queue = deque(state['queue'])
            self.plans = {int(i): p for i, p in state['plans'].items()}
            self.removed, self.steps = list(state['removed']), state['steps']
            if (len(self.removed) != len(set(self.removed)) or
                    self.alive & set(self.removed) or
                    self.alive | set(self.removed) != set(range(size)) or
                    len(self.queue) != len(set(self.queue)) or
                    not set(self.queue) <= set(range(size)) or not self.plans.keys() <= self.alive):
                raise ValueError('invalid closure checkpoint')
        self.queued = set(self.queue)
        self.parents = defaultdict(set)
        for i, plan in self.plans.items():
            for j in plan['dependencies']:
                self.parents[j].add(i)

    @property
    def finished(self):
        return not self.queue and not self.dirty

    def step(self):
        if not self.queue:
            return False
        i = self.queue[0]
        # Do not consume a query until it finishes. Resource errors and user
        # interruption must never silently turn it into a negative answer.
        proposal = self.oracle(i, self.alive) if i in self.alive else None
        self.dirty = True
        self.queue.popleft()
        self.queued.remove(i)
        if i not in self.alive:
            self.dirty = False
            return True
        self.steps += 1
        for child in self.plans.get(i, {}).get('dependencies', []):
            self.parents[child].discard(i)
        if proposal is None:
            self.alive.remove(i)
            self.removed.append(i)
            self.plans.pop(i, None)
            for parent in sorted(self.parents[i]):
                if parent in self.alive and parent not in self.queued:
                    self.queue.append(parent)
                    self.queued.add(parent)
        else:
            if not set(proposal['dependencies']) <= self.alive:
                raise ValueError('oracle returned a rule outside the current universe')
            self.plans[i] = copy.deepcopy(proposal)
            for child in proposal['dependencies']:
                self.parents[child].add(i)
        self.dirty = False
        return True

    def snapshot(self):
        if self.dirty:
            # A signal during the tiny commit section may leave queue/parent
            # metadata incomplete. Retain only fully recorded eliminations;
            # re-query every surviving type on resume. No type is skipped.
            alive = sorted(set(range(self.size))-set(self.removed))
            return dict(size=self.size, alive=alive, queue=alive, plans={},
                        removed=self.removed[:], steps=self.steps)
        return dict(size=self.size, alive=sorted(self.alive), queue=list(self.queue),
                    plans=copy.deepcopy(self.plans), removed=self.removed[:], steps=self.steps)


def build_bank(graphs, progress=None):
    data = dict(format=FORMAT, cells=[], nodes=[], roots={})
    domains, types, mappings, checkers, sources = {}, {}, [], [], []
    root_options = dict(zero=[], positive=[])
    pools, layouts = defaultdict(dict), defaultdict(set)

    def register(domain):
        if domain not in domains:
            domains[domain] = len(data['cells'])
            data['cells'].append(domain.record())
        return domains[domain]

    for graph in graphs:
        checker = PiecewiseVerifier(graph)
        audit = checker.audit()
        if audit['failed_rules']:
            raise ValueError('invalid source local rule')
        mapping, cellmap = [], [register(d) for d in checker.cells]
        for i, node in enumerate(checker.nodes):
            _, domain, lower, upper = checker.node(i)
            key = (domain, lower, upper)
            if key not in types:
                types[key] = len(data['nodes'])
                data['nodes'].append(dict(cell=cellmap[node['cell']], lower=node['lower'],
                                         upper=node['upper'], children=[]))
            mapping.append(types[key])
        for name, index in graph['roots'].items():
            root_options[name].append(mapping[index])
        mappings.append((mapping, cellmap))
        checkers.append(checker)
        sources.append(dict(proof_hash=checker.proof_hash(), nodes=len(checker.nodes),
                            verified_local=len(audit['verified_rules']), failed=0))
        if progress:
            progress(dict(stage='source audited', **sources[-1]))
    for checker, (mapping, cellmap) in zip(checkers, mappings):
        for node in checker.nodes:
            if node.get('pieces'):
                layouts[cellmap[node['cell']]].add(tuple(cellmap[p['cell']] for p in node['pieces']))
            for rule in rules(node):
                cid = cellmap[rule['cell']]
                domain = checker.cells[rule['cell']]
                for e in rule['children']:
                    # Offers with equal literal descriptions share all their
                    # destination options. Keeping extra encodings is harmless.
                    body = {k: copy.deepcopy(e[k]) for k in ('suffixes', 'high', 'lower', 'upper')}
                    # Equality of mathematical alternatives must not assume
                    # a collision-free cryptographic hash.
                    key = json.dumps(body, sort_keys=True, separators=(',', ':'))
                    if key not in pools[cid]:
                        pools[cid][key] = dict(body, destinations=[])
                    dests = pools[cid][key]['destinations']
                    for d in e['destinations']:
                        dest = dict(node=mapping[d['node']], swap=d['swap'])
                        if dest not in dests:
                            dests.append(dest)
    root_options = {k: sorted(set(v)) for k, v in root_options.items()}
    data['roots'] = {k: v[0] for k, v in root_options.items()}
    bank = dict(format='freiman-complete-library-v1', graph=data, sources=sources,
                root_options=root_options,
                offers={str(k): list(v.values()) for k, v in sorted(pools.items())},
                layouts={str(k): [list(x) for x in sorted(v)] for k, v in sorted(layouts.items())},
                scope='all chains of saved offers on the exact same domain; all saved destination subsets; all saved guard layouts')
    # Every input edge was checked above. Merging only unions individually
    # admissible destinations of the same offered interval on the same domain.
    bank['bank_hash'] = digest(bank)
    return bank


class ExactLibrary:
    def __init__(self, bank):
        if bank['format'] != 'freiman-complete-library-v1':
            raise ValueError('unknown library format')
        if digest({k: v for k, v in bank.items() if k != 'bank_hash'}) != bank['bank_hash']:
            raise ValueError('library hash mismatch')
        self.bank = bank
        self.checker = PiecewiseVerifier(copy.deepcopy(bank['graph']))
        self.offers = {int(k): v for k, v in bank['offers'].items()}
        self.layouts = {int(k): v for k, v in bank['layouts'].items()}
        self.usable_cache = {}
        self.statistics = dict(queries=0, child_checks=0, child_failures=0, cover_queries=0)

    def usable(self, cid, alive):
        result = []
        domain = self.checker.cells[cid]
        for position, offer in enumerate(self.offers.get(cid, [])):
            retained = tuple(i for i, d in enumerate(offer['destinations']) if d['node'] in alive)
            if not retained:
                continue
            key = cid, position, retained
            if key not in self.usable_cache:
                edge = dict(offer, destinations=[offer['destinations'][j] for j in retained])
                self.statistics['child_checks'] += 1
                try:
                    a, b, deps = self.checker.child(domain, edge)
                except ValueError:
                    self.statistics['child_failures'] += 1
                    self.usable_cache[key] = None
                else:
                    self.usable_cache[key] = (a, b, edge)
            found = self.usable_cache[key]
            if found is not None:
                result.append(found)
        return result

    def cover(self, cid, lower, upper, alive):
        """Exhaustive endpoint reachability, no beam or midpoint ordering."""
        self.statistics['cover_queries'] += 1
        domain = self.checker.cells[cid]
        usable = self.usable(cid, alive)
        predecessor, todo = {lower: None}, deque([lower])
        while todo:
            current = todo.popleft()
            if compare(domain, current, upper):
                path = []
                while predecessor[current] is not None:
                    previous, edge = predecessor[current]
                    path.append(edge)
                    current = previous
                return path[::-1]
            for a, b, edge in usable:
                if b not in predecessor and compare(domain, current, a) and compare(domain, b, current, strict=True):
                    predecessor[b] = current, edge
                    todo.append(b)
        return None

    def query(self, i, alive):
        self.statistics['queries'] += 1
        node, domain, lower, upper = self.checker.node(i)
        plan = self.cover(node['cell'], lower, upper, alive)
        payload = None if plan is None else dict(children=plan)
        if payload is None:
            for layout in self.layouts.get(node['cell'], []):
                pieces = []
                for cid in layout:
                    plan = self.cover(cid, lower, upper, alive)
                    if plan is None:
                        break
                    pieces.append(dict(cell=cid, children=plan))
                else:
                    payload = dict(children=[], pieces=pieces)
                    break
        if payload is None:
            return None
        # Validate the assembled rule independently. An internal error must
        # abort; it must not be converted into a spurious nonexistence result.
        old = self.checker.nodes[i]
        self.checker.nodes[i] = dict(old, **payload)
        self.checker.checked.pop(i, None)
        try:
            verification = self.checker.local(i)
        finally:
            self.checker.nodes[i] = old
            self.checker.checked.pop(i, None)
        return dict(payload=payload, dependencies=verification['dependencies'])

    def outcome(self, solver):
        choices = {name: [i for i in options if i in solver.alive]
                   for name, options in self.bank['root_options'].items()}
        return dict(finite_menu_exhausted=solver.finished, remaining_candidates=len(solver.alive),
                    eliminated=len(solver.removed), steps=solver.steps, pending=len(solver.queue),
                    surviving_root_options=choices,
                    closed_in_this_menu=all(choices.values()) if solver.finished else None)

    def certificate(self, solver):
        outcome = self.outcome(solver)
        if not outcome['closed_in_this_menu']:
            raise ValueError('no completed closed library result')
        graph = copy.deepcopy(self.bank['graph'])
        for i, plan in solver.plans.items():
            graph['nodes'][i].update(copy.deepcopy(plan['payload']))
        graph['roots'] = {name: options[0] for name, options in outcome['surviving_root_options'].items()}
        graph = prune(graph)
        verification = PiecewiseVerifier(graph).closed()
        return graph, verification

    def verify_fixed_point(self, solver):
        """Replay the elimination certificate from the full finite universe."""
        if not solver.finished:
            raise ValueError('unfinished elimination is not a negative certificate')
        replay = ExactLibrary(self.bank)
        alive = set(range(len(self.checker.nodes)))
        for i in solver.removed:
            if i not in alive or replay.query(i, alive) is not None:
                raise ValueError('invalid elimination step')
            alive.remove(i)
        if alive != solver.alive:
            raise ValueError('wrong greatest-fixed-point remainder')
        for i in sorted(alive):
            if replay.query(i, alive) is None:
                raise ValueError('remainder is not closed')
        return dict(bank_hash=self.bank['bank_hash'], eliminated_replayed=len(solver.removed),
                    surviving_rules_replayed=len(alive), failed=0,
                    status='exact greatest fixed point of this finite menu; no conclusion about larger menus')
