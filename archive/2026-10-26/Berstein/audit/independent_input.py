"""Independent exact audit of graph_wide's mathematical input semantics.

Only Python's standard library is imported. In particular, none of the
Freiman/Berstein generators, field classes, automata, or checkers are used.
This verifies the data meanings, not the graph covering inequalities.

For a word a, write F_a(x)=(A*x+B)/(C*x+D), r=C/D, and let x0 be
the tail attaining the lower endpoint of its cylinder. The graph coordinate
is the positive derivative ratio |F_b'(y0)|/|F_a'(x0)|. If u has matrix
(a,b;c,d), and y0 is the child anchor, then the child's derivative divided
by the parent's derivative is

    ((1+r*x0)/((c+r*a)*y0+d+r*b))**2.

Its denominator is positive; its unsquared expression is a Mobius function
of r, hence is monotone or constant. It is constant precisely when
x0*(c*y0+d) == a*y0+b. Constant IDs are checked using that symbolic identity,
not merely rounded endpoint agreement. All shared raw endpoint IDs are
also checked by exact equality, so cancellation using their IDs is valid.

Greedy continued-fraction extrema are exact: order alternates with position,
and every allowed finite word can be continued by 2 forever. The finite
state (forbidden-prefix suffix, position parity) eventually repeats. We
solve the resulting periodic CF equation algebraically and verify its
unique positive root. Integer discriminants here lie in Q(sqrt(462)).

The width/eta input fields are parsed and checked for elementary bounds,
but their precise meanings are not needed by graph_kernel's coverage
predicates: width is used only to fill an otherwise unread actual_ratio
array, and eta is not read after parsing. This is not an audit of another
kernel that might use those fields.
"""

import argparse
import copy
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache, total_ordering
from itertools import product
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEN = 1 << 48
BAD = (3, 1, 3, 1, 3)


@total_ordering
@dataclass(frozen=True)
class Exact:
    """An independently implemented element a+b*sqrt(462)."""

    a: Q = Q(0)
    b: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', Q(self.a))
        object.__setattr__(self, 'b', Q(self.b))

    @staticmethod
    def cast(value):
        return value if isinstance(value, Exact) else Exact(value)

    def __add__(self, other):
        other = self.cast(other)
        return Exact(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Exact(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        return Exact(self.a * other.a + 462 * self.b * other.b,
                     self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        norm = other.a * other.a - 462 * other.b * other.b
        if not norm:
            raise ZeroDivisionError
        return self * Exact(other.a / norm, -other.b / norm)

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def __eq__(self, other):
        other = self.cast(other)
        return self.a == other.a and self.b == other.b

    def __lt__(self, other):
        a, b = (self - other).a, (self - other).b
        if b == 0:
            return a < 0
        if a == 0:
            return b < 0
        if a >= 0 and b >= 0:
            return False
        if a <= 0 and b <= 0:
            return True
        # Opposite signs: squaring compares their positive magnitudes.
        return a * a < 462 * b * b if a > 0 else a * a > 462 * b * b

    def pair(self):
        return [str(self.a), str(self.b)]

    def __float__(self):
        return float(self.a) + float(self.b) * 462 ** 0.5


def demand(condition, message):
    if not condition:
        raise AssertionError(message)


def legal(word):
    return not any(word[i:i + 5] == BAD for i in range(len(word) - 4))


def state(word):
    if not legal(word):
        return None
    return max(j for j in range(5) if not j or word[-j:] == BAD[:j])


def cf(word, tail):
    for digit in reversed(word):
        tail = 1 / (digit + tail)
    return tail


@lru_cache(None)
def matrix(word):
    # Explicit multiplication by [[0,1],[1,d]], in reading order.
    z = ((1, 0), (0, 1))
    for digit in word:
        z = ((z[0][1], z[0][0] + digit * z[0][1]),
             (z[1][1], z[1][0] + digit * z[1][1]))
    return z[0][0], z[0][1], z[1][0], z[1][1]


@lru_cache(None)
def greedy_cycle(q, minimize):
    """Return preperiod and period using direct string legality."""
    seen, digits, parity = {}, [], 0
    while (q, parity) not in seen:
        seen[q, parity] = len(digits)
        options = [d for d in (1, 2, 3) if legal(BAD[:q] + (d,))]
        digit = max(options) if minimize == (parity == 0) else min(options)
        digits.append(digit)
        q = state(BAD[:q] + (digit,))
        parity ^= 1
    cut = seen[q, parity]
    return tuple(digits[:cut]), tuple(digits[cut:])


@lru_cache(None)
def extreme(q, minimize):
    prefix, period = greedy_cycle(q, minimize)
    a, b, c, d = matrix(period)
    discriminant = (d - a) ** 2 + 4 * c * b
    multiplier = isqrt(discriminant // 462)
    demand(discriminant == 462 * multiplier * multiplier,
           'Periodic discriminant not in the implemented field')
    positive_root = Exact(Q(a - d, 2 * c), Q(multiplier, 2 * c))
    demand(b > 0 and c > 0 and 0 < positive_root < 1,
           'Periodic root is not the unique positive CF root')
    demand(cf(period, positive_root) == positive_root, 'Periodic fixed point')
    result = cf(prefix, positive_root)
    # A second arithmetic route: a rational CF cylinder around 100 digits.
    digits = prefix + (period * (101 // len(period) + 1))[:100]
    outer = sorted(cf(digits, t) for t in (Q(0), Q(1)))
    demand(outer[0] <= result <= outer[1], 'Periodic rational cross-check')
    return result


def encloses(interval, value):
    return interval[0] <= value <= interval[1]


def contains(outer, inner):
    return outer[0] <= inner[0] <= inner[1] <= outer[1]


def parse_input(path):
    tokens = iter(path.read_text().split())
    demand(next(tokens) == 'FREIMAN_DYADIC_GRAPH_V1', 'Input magic')

    def integer():
        return int(next(tokens))

    def interval():
        lo, hi = Q(integer(), DEN), Q(integer(), DEN)
        demand(lo <= hi, 'Reversed input interval')
        return lo, hi

    s, e, low, high, types, pairs, root = [integer() for _ in range(7)]
    data = dict(s=s, e=e, low=low, high=high, types=types, root=root)
    data['bands'] = [interval() for _ in range(types)]
    data['pairs'] = [tuple(integer() for _ in range(3)) for _ in range(pairs)]
    data['powers'] = [interval() for _ in range(high - low + 2)]
    data['sides'] = []
    for _ in range(s):
        width = interval()
        parity, shape, anchor = integer(), interval(), integer()
        tails = [interval() for _ in range(integer())]
        extensions = []
        for _ in range(e):
            child = integer()
            if child < 0:
                demand(child == -1, 'Invalid absent-child marker')
                extensions.append(None)
            else:
                spine, constant = integer(), integer()
                scale, eta = interval(), [interval(), interval()]
                endpoints = [integer(), integer()]
                extensions.append(dict(child=child, spine=spine, constant=constant,
                                       scale=scale, eta=eta, endpoints=endpoints))
        data['sides'].append(dict(width=width, parity=parity, shape=shape,
                                  anchor=anchor, tails=tails, extensions=extensions))
    demand(next(tokens, None) is None, 'Unparsed trailing input')
    return data


def audit_automaton():
    # A forbidden word has length 5. Last 4 letters determine its new
    # occurrence; their longest BAD-prefix suffix is sufficient. Enumerate
    # every such context, including the allowed fixed digit 4.
    contexts = 0
    for length in range(5):
        for word in product((1, 2, 3, 4), repeat=length):
            q = state(word)
            for d in (1, 2, 3, 4):
                demand(state(word + (d,)) == state(BAD[:q] + (d,)),
                       'Suffix state loses an automaton transition')
            demand(state(word + (2,)) == 0, '2 does not reset state')
            contexts += 1
    for q in range(5):
        demand(0 < extreme(q, True) < extreme(q, False) < 1, 'Extremal order')
    return contexts


def audit_semantics(data, meta):
    keys = [(q, parity, tuple(suffix)) for q, parity, suffix in meta['side_keys']]
    prototypes = [tuple(w) for w in meta['prototypes']]
    extensions = [tuple(w) for w in meta['extensions']]
    indices = {key: i for i, key in enumerate(keys)}
    s, e = data['s'], data['e']
    memory = meta['memory']
    demand(s == len(keys) == len(indices) == len(prototypes), 'Side count/uniqueness')
    demand(e == len(extensions) == len(set(extensions)), 'Extension count/uniqueness')
    demand(memory == 2 and extensions[0] == (), 'Memory or empty extension')
    demand(all(d in (1, 2, 3) for u in extensions for d in u), 'Extension alphabet')
    demand(meta['scale'] == DEN, 'Dyadic denominator')
    demand(meta['coordinate'] == 'lower_endpoint_derivative_ratio', 'Coordinate')
    demand(data['low'] == meta['low'] and data['high'] == meta['high'], 'Scale grid')
    demand(data['root'] == meta['root_geometry_id'], 'Original root cell metadata')
    demand(data['pairs'] == [tuple(p) for p in meta['successor_pairs']], 'Pair metadata')
    for u, w, flag in data['pairs']:
        demand(0 <= u < e and 0 <= w < e and flag in (0, 1), 'Pair indices/flag')
        demand(len(extensions[u]) + len(extensions[w]) > 0, 'No progress in successor')
    expected_bands = [(Q(0), Q(1))] + [(Q(j, 32), Q(j + 2, 32)) for j in range(31)]
    demand(data['types'] == 32 and data['bands'] == expected_bands, 'Band semantics')
    demand(data['bands'] == [tuple(map(Q, x)) for x in meta['bands']], 'Band metadata')
    base = Q(meta['base'])
    demand(base == Q(51, 50), 'Unexpected scale base')
    for exponent, interval in zip(range(data['low'], data['high'] + 2), data['powers']):
        demand(encloses(interval, base ** exponent), 'Power enclosure')
    prehistory = tuple(map(Q, meta['prehistory_interval']))
    demand(prehistory == (Q(1, 4), Q(4, 5)), 'Prehistory bounds')
    for digit in (1, 2, 3):
        demand(contains(prehistory, (1 / (digit + prehistory[1]),
                                    1 / (digit + prehistory[0]))), 'Prehistory invariance')

    shapes, anchors, exact_tails = [], [], []
    transition_count = endpoint_references = alias_references = 0
    for i, (q, parity, suffix) in enumerate(keys):
        side, prototype = data['sides'][i], prototypes[i]
        demand(q in range(5) and parity in (0, 1) and len(suffix) == memory, 'Side key')
        demand(state(prototype) == q and len(prototype) % 2 == parity
               and prototype[-memory:] == suffix, 'Prototype key')
        demand(side['parity'] == parity, 'Stored parity')
        # If q > memory, q itself determines the longer suffix. Otherwise
        # the memory suffix determines it. No hidden prototype digits enter.
        defining_suffix = BAD[:q] if q > memory else suffix
        demand(prototype[-max(memory, q):] == defining_suffix, 'Uniform suffix representation')
        shape = tuple(sorted(cf(defining_suffix[::-1], x) for x in prehistory))
        demand(contains(side['shape'], shape), 'Shape enclosure')
        demand(0 < shape[0] < shape[1] < 1, 'Nondegenerate positive shape')
        shapes.append(shape)
        anchor = extreme(q, parity == 0)
        anchors.append(anchor)
        assigned = {}
        prefix, period = greedy_cycle(q, parity == 0)
        depth = meta['spine_depth']
        spine = (prefix + period * (depth + 1))[:depth]
        demand(side['width'][0] > 0, 'Width positivity')
        for extension_id, u in enumerate(extensions):
            qchild = state(BAD[:q] + u)
            record = side['extensions'][extension_id]
            if qchild is None:
                demand(record is None, 'Illegal word exported as a child')
                continue
            demand(record is not None, 'Missing legal extension')
            child_key = (qchild, (parity + len(u)) % 2, (suffix + u)[-memory:])
            demand(record['child'] == indices[child_key], 'Child identity')
            demand(record['constant'] >= 0, 'Negative constant ID')
            demand(record['scale'][0] > 0, 'Derivative scale positivity')
            demand(all(contains((Q(0), Q(1)), x) for x in record['eta']), 'Eta bounds')
            expected_spine = bool(u) and len(u) <= depth and u[:-1] == spine[:len(u) - 1]
            demand(record['spine'] == int(expected_spine), 'Spine flag')
            endpoints = sorted(cf(u, extreme(qchild, minimum)) for minimum in (True, False))
            if parity:
                endpoints.reverse()
            for value, raw_id in zip(endpoints, record['endpoints']):
                demand(0 <= raw_id < len(side['tails']), 'Raw endpoint index')
                if raw_id in assigned:
                    demand(assigned[raw_id] == value, 'Shared raw ID aliases unequal endpoints')
                    alias_references += 1
                else:
                    assigned[raw_id] = value
                demand(encloses(side['tails'][raw_id], value), 'Raw endpoint enclosure')
                endpoint_references += 1
            transition_count += 1
        demand(set(assigned) == set(range(len(side['tails']))), 'Unidentified raw endpoints')
        demand(len(set(assigned.values())) == len(assigned), 'Duplicate exact raw IDs')
        demand(side['anchor'] in assigned and assigned[side['anchor']] == anchor,
               'Anchor identity')
        demand(side['extensions'][0]['endpoints'][0] == side['anchor'], 'Empty-word anchor ID')
        exact_tails.append(assigned)

    constants = {}
    constant_references = 0
    for i, side in enumerate(data['sides']):
        for u, record in zip(extensions, side['extensions']):
            if record is None:
                continue
            child = record['child']
            a, b, c, d = matrix(u)
            demand(a * d - b * c == (-1) ** len(u), 'CF determinant/parity')
            newshape = tuple(sorted((c + r * a) / (d + r * b) for r in shapes[i]))
            demand(contains(shapes[child], newshape), 'Exact child shape inclusion')
            x, y = anchors[i], anchors[child]
            denominator0, denominator1 = c * y + d, a * y + b
            demand(denominator0 > 0 and denominator1 >= 0, 'Derivative denominator')
            determinant = x * denominator0 - denominator1
            values = []
            for r in shapes[i]:
                ratio = (1 + r * x) / (denominator0 + r * denominator1)
                value = ratio * ratio
                demand(encloses(record['scale'], value), 'Derivative scale enclosure')
                values.append(value)
            # Fractional linear monotonicity, and positivity, justify both
            # endpoint extrema. An exact zero determinant is the only reason
            # that equal constant IDs may cancel the derivative ratio.
            demand((values[0] == values[1]) == (determinant == 0),
                   'Constant scale symbolic criterion')
            constant_id = record['constant']
            demand(bool(constant_id) == (determinant == 0), 'Spurious/missing constant ID')
            if constant_id:
                value = 1 / (denominator0 * denominator0)
                demand(value == values[0] == values[1], 'Constant scale value')
                if constant_id in constants:
                    demand(constants[constant_id] == value,
                           'Global constant ID aliases unequal derivative factors')
                else:
                    constants[constant_id] = value
                constant_references += 1
    demand(len(set(constants.values())) == len(constants), 'Duplicate constant values')
    return dict(shapes=shapes, anchors=anchors, indices=indices, constants=constants,
                transitions=transition_count, endpoint_references=endpoint_references,
                raw_tail_count=sum(len(x) for x in exact_tails),
                exact_alias_references=alias_references, constant_references=constant_references)


def audit_root(data, meta, semantic, alive_path):
    a, b = (3, 2, 2), (4, 3, 1)
    ids = [semantic['indices'][(state(w), len(w) % 2, w[-2:])] for w in (a, b)]
    ma, mb = matrix(a), matrix(b)
    r, s = Q(ma[2], ma[3]), Q(mb[2], mb[3])
    rho = Q(ma[3] * ma[3], mb[3] * mb[3])
    demand((r, s, rho) == (Q(7, 17), Q(13, 17), Q(1)), 'Root continuants')
    demand(encloses(semantic['shapes'][ids[0]], r)
           and encloses(semantic['shapes'][ids[1]], s), 'Root shape membership')
    x, y = [semantic['anchors'][i] for i in ids]
    z = (1 + r * x) / (1 + s * y)
    scale = rho * z * z
    demand(scale == Exact(Q(55792801, 159491641), Q(2467176, 159491641)),
           'Documented root derivative-ratio formula')
    demand(Q(51, 50) ** -20 <= scale <= Q(51, 50) ** -19, 'Root scale membership')
    bins = data['high'] - data['low'] + 1
    geometry = ids[0] * data['s'] + ids[1]
    demand(geometry == 193, 'Root geometry')
    alive = alive_path.read_bytes()
    demand(len(alive) == data['s'] ** 2 * bins * data['types'], 'Alive table size')
    demand(all(x in (0, 1) for x in alive), 'Alive flags')
    cell = geometry * bins - 20 - data['low']
    target_bands = list(range(3, 28))
    demand(all(alive[cell * data['types'] + t] for t in target_bands), 'Missing root bands')
    bands = [data['bands'][t] for t in target_bands]
    demand(bands[0][0] == Q(1, 16) and bands[-1][1] == Q(7, 8)
           and all(a[1] >= b[0] for a, b in zip(bands, bands[1:])), 'Root band union')
    endpoints = [sorted(cf(w, extreme(state(w), minimize)) for minimize in (True, False))
                 for w in (a, b)]
    lower, upper = [endpoints[0][j] + endpoints[1][j] for j in (0, 1)]
    demand(lower == Exact(Q(8512493, 17339617), Q(28004, 17339617)),
           'Documented root hull lower endpoint formula')
    demand(upper == Exact(Q(1352829, 2233974), Q(-8081, 2233974)),
           'Documented root hull upper endpoint formula')
    interval = (4 + lower + (upper - lower) / 16, 4 + lower + 7 * (upper - lower) / 8)
    freiman = Exact(Q(2221564096, 491993569), Q(283748, 491993569))
    demand(interval[0] < Q('4.52578') < Q('4.52754') < interval[1] < freiman,
           'Claimed rational interval or Freiman comparison')
    return dict(words=['322', '431'], side_ids=ids, geometry=geometry, bin=-20,
                r=str(r), s=str(s), scale=scale.pair(), bands=len(target_bands),
                exact_interval=[x.pair() for x in interval],
                approximate_interval=[float(x) for x in interval],
                alive_count=sum(alive),
                scope='Initial row membership only; closure is checked separately.')


def negative_controls(data, meta):
    """Mutate in memory only, and require the full semantics audit to reject."""
    controls = []
    wrong_alias = copy.deepcopy(data)
    wrong_alias['sides'][0]['extensions'][0]['endpoints'][1] = \
        wrong_alias['sides'][0]['extensions'][0]['endpoints'][0]
    controls.append(('unequal_raw_endpoints_share_id', wrong_alias,
                     'Shared raw ID aliases unequal endpoints'))
    spurious = copy.deepcopy(data)
    record = next(x for side in spurious['sides'] for x in side['extensions']
                  if x is not None and x['constant'] == 0)
    record['constant'] = 1
    controls.append(('nonconstant_derivative_tagged_constant', spurious,
                     'Spurious/missing constant ID'))
    unequal = copy.deepcopy(data)
    record = next(x for side in unequal['sides'] for x in side['extensions']
                  if x is not None and x['constant'] > 1)
    record['constant'] = 1
    controls.append(('unequal_constants_share_id', unequal,
                     'Global constant ID aliases unequal derivative factors'))
    results = {}
    for name, damaged, expected in controls:
        try:
            audit_semantics(damaged, meta)
        except AssertionError as failure:
            demand(str(failure) == expected, 'Control failed for an unexpected reason')
            results[name] = str(failure)
        else:
            raise AssertionError('Negative control accepted: ' + name)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=ROOT / 'Freiman/data/graph_wide.dat')
    parser.add_argument('--meta', type=Path, default=ROOT / 'Freiman/data/graph_wide.meta.json')
    parser.add_argument('--alive', type=Path, default=ROOT / 'Freiman/data/graph_wide.json.alive.bin')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    contexts = audit_automaton()
    data, meta = parse_input(args.input), json.loads(args.meta.read_text())
    semantic = audit_semantics(data, meta)
    root = audit_root(data, meta, semantic, args.alive)
    controls = negative_controls(data, meta)
    report = dict(passed=True, arithmetic='Independent exact Q(sqrt(462)); stdlib only',
                  repository_math_imports=False, finite_automaton_contexts=contexts,
                  side_states=data['s'], extension_words=data['e'],
                  valid_side_transitions=semantic['transitions'],
                  raw_endpoint_references=semantic['endpoint_references'],
                  raw_tail_ids=semantic['raw_tail_count'],
                  exact_alias_references=semantic['exact_alias_references'],
                  derivative_constant_references=semantic['constant_references'],
                  derivative_constant_groups=len(semantic['constants']),
                  derivative_constants={str(k): v.pair() for k, v in semantic['constants'].items()},
                  constant_identity_method='Exact symbolic Mobius determinant and global equality',
                  uniform_suffix_shapes_and_all_child_inclusions=True,
                  greedy_extremes=[dict(state=q, minimum=minimum,
                                       prefix=list(greedy_cycle(q, minimum)[0]),
                                       period=list(greedy_cycle(q, minimum)[1]),
                                       exact=extreme(q, minimum).pair())
                                   for q in range(5) for minimum in (True, False)],
                  initial_root=root, negative_controls=controls,
                  unused_fields='Width and eta mathematical values not audited; graph coverage does not read them.',
                  does_not_certify='Graph inequality/coverage closure or spectral domination.',
                  sha256={str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path):
                          hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in (args.input, args.meta, args.alive, Path(__file__).resolve())})
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('greedy_extremes', 'sha256', 'derivative_constants')}, indent=2))


if __name__ == '__main__':
    main()
