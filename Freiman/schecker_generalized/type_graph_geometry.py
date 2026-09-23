"""Exact geometry for cyclic interval types over Q(sqrt(462)).

No filling claims are assumed here. A box describes r, s and the ratio of
absolute derivatives at the chosen extremal anchors. Endpoints may also be
interpolated inside a legal tail hull; they need not themselves be Cantor points.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache

from explore import Q, extreme_tail, matrix, state_of, transform
from adaptive_types import affine_rows


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encode(x):
    x = Q.coerce(x)
    return [str(x.a), str(x.b)]


def decode(x):
    require(isinstance(x, list) and len(x) == 2, 'invalid field element')
    return Q(F(x[0]), F(x[1]))


def square(x):
    return x*x


@lru_cache(None)
def anchor(state, high):
    return extreme_tail(state_of(state), high)[0]


@dataclass(frozen=True)
class Cell:
    states: tuple
    parity: int
    high: bool
    r: tuple
    s: tuple
    ratio: tuple

    def validate(self):
        require(len(self.states) == 2, 'two states required')
        for state in self.states:
            require(isinstance(state, str) and all(c in '123' for c in state),
                    'invalid state word')
            state_of(state)
        require(type(self.parity) is int and self.parity in (-1, 1), 'invalid parity')
        require(type(self.high) is bool, 'invalid anchor choice')
        for lo, hi in (self.r, self.s):
            require(Q(F(1, 4)) <= lo <= hi <= 1, 'shape box outside [1/4,1]')
        require(0 < self.ratio[0] <= self.ratio[1], 'positive ratio required')
        return self

    def anchors(self):
        return (anchor(self.states[0], self.high),
                anchor(self.states[1], self.high if self.parity > 0 else not self.high))

    def record(self):
        return dict(states=self.states, parity=self.parity, high=self.high,
                    r=list(map(encode, self.r)), s=list(map(encode, self.s)),
                    ratio=list(map(encode, self.ratio)))

    @classmethod
    def read(cls, data):
        return cls(tuple(data['states']), data['parity'], data['high'],
                   tuple(map(decode, data['r'])), tuple(map(decode, data['s'])),
                   tuple(map(decode, data['ratio']))).validate()


@lru_cache(maxsize=200000)
def tail(state, word, high):
    require(isinstance(word, str) and type(high) is bool, 'invalid endpoint label')
    if '@' in word:
        prefix, weight = word.split('@')
        weight = F(weight)
        require(0 <= weight <= 1, 'interpolation outside the hull')
    else:
        prefix, weight = word, None
    require(all(c in '123' for c in prefix), 'illegal appended digit')
    end = state_of(state+prefix)
    x = anchor(end, high) if weight is None else (
        (1-weight)*anchor(end, False)+weight*anchor(end, True))
    return transform(prefix, x)


def endpoint(states, label, suffixes=('', '')):
    require(len(label) == 4, 'invalid endpoint arity')
    u, h, v, k = label
    return (tail(states[0], suffixes[0]+u, h),
            tail(states[1], suffixes[1]+v, k))


def full_labels(parity):
    return (('', False, '', parity < 0), ('', True, '', parity > 0))


def exchange(label):
    return tuple(label[2:])+tuple(label[:2])


@lru_cache(maxsize=200000)
def delta_range(alpha, x, y, box):
    if x == y:
        return Q(), Q()
    points = list(box)
    coefficient = alpha*(x+y)-2*x*y
    if coefficient != 0:
        critical = (x+y-2*alpha)/coefficient
        if box[0] < critical < box[1]:
            points.append(critical)
    values = [(x-y)*square(1+alpha*r)/((1+x*r)*(1+y*r)) for r in points]
    return min(values), max(values)


@lru_cache(maxsize=200000)
def difference_range(cell, a, b):
    alpha, beta = cell.anchors()
    dl = delta_range(alpha, a[0], b[0], cell.r)
    dr = delta_range(beta, a[1], b[1], cell.s)
    if cell.parity < 0:
        dr = -dr[1], -dr[0]
    values = [q*d for q in cell.ratio for d in dr]
    return dl[0]+min(values), dl[1]+max(values)


def ge(cell, a, b, strict=False):
    low = difference_range(cell, a, b)[0]
    return low > 0 if strict else low >= 0


@lru_cache(maxsize=200000)
def shape_image(word, box):
    a, b, c, d = matrix(word)
    values = [(a*r+c)/(b*r+d) for r in box]
    return min(values), max(values)


@lru_cache(maxsize=200000)
def factor_range(word, box, old_anchor, new_anchor):
    a, b, c, d = matrix(word)
    # Exact equality preserves the common eigenvalue on periodic returns.
    values = [(r*(a*new_anchor+b)+c*new_anchor+d)/(1+r*old_anchor) for r in box]
    require(min(values) > 0, 'nonpositive derivative factor')
    return min(values), max(values)


@lru_cache(maxsize=200000)
def transition(cell, u, v, child_high):
    require(type(child_high) is bool, 'invalid child anchor choice')
    require(bool(u or v) and all(c in '123' for c in u+v), 'empty or illegal successor')
    states = tuple(state_of(s+w) for s, w in zip(cell.states, (u, v)))
    p = cell.parity*(-1)**(len(u)+len(v))
    old_a, old_b = cell.anchors()
    new_a = anchor(states[0], child_high)
    new_b = anchor(states[1], child_high if p > 0 else not child_high)
    left = factor_range(u, cell.r, old_a, new_a)
    right = factor_range(v, cell.s, old_b, new_b)
    ratios = (cell.ratio[0]*square(left[0]/right[1]),
              cell.ratio[1]*square(left[1]/right[0]))
    return Cell(states, p, child_high, shape_image(u, cell.r),
                shape_image(v, cell.s), ratios).validate()


def swapped(cell):
    return Cell(cell.states[::-1], cell.parity,
                cell.high if cell.parity > 0 else not cell.high,
                cell.s, cell.r, (1/cell.ratio[1], 1/cell.ratio[0]))


def parameters(u, v, high=True):
    states = tuple(map(state_of, (u, v)))
    p = (-1)**(len(u)+len(v))
    alpha, beta = anchor(states[0], high), anchor(states[1], high if p > 0 else not high)
    _, _, c, d = matrix(u)
    _, _, e, f = matrix(v)
    ratio = square((c*alpha+d)/(e*beta+f))
    return Cell(states, p, high, (Q(F(c, d)),)*2, (Q(F(e, f)),)*2,
                (ratio,)*2).validate()


@lru_cache(None)
def root_cells():
    """Rigorous boxes for A_0 and all A_n, n>=1, including the limiting pair."""
    zero = parameters('32113', '4322')
    alpha, beta = zero.anchors()
    lam = Q(43, 2)
    for word, z in (('131213', alpha), ('313121', beta)):
        a, b, c, d = matrix(word)
        require(a*z+b == lam*z and c*z+d == lam, 'periodic invariant failed')
    tau = Q(43, -2)
    require(0 < tau < Q(F(1, 85)) and tau*(86-tau) == 1, 'invalid recurrence limit')
    ranges = []
    for (c0, c1), (d0, d1) in affine_rows('', ''):
        values = [(c0+c1*t)/(d0+d1*t) for t in (Q(), tau)]
        ranges.append((min(values), max(values)))
    positive = Cell(zero.states, -1, True, *ranges, zero.ratio).validate()
    return zero, positive
