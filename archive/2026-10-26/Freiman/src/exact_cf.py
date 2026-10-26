"""Exact Q(sqrt(462)) arithmetic for the 31313 language.

No floats are used for signs, interval contact, or certificate decisions.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache, total_ordering
from math import isqrt
from obstruction_probe import scan, step, extremal_tail


@total_ordering
@dataclass(frozen=True)
class K:
    a: Q = Q(0)
    b: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', Q(self.a))
        object.__setattr__(self, 'b', Q(self.b))

    @staticmethod
    def cast(x):
        return x if isinstance(x, K) else K(x)

    def __add__(self, other):
        other = self.cast(other)
        return K(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        return K(self.a * other.a + 462 * self.b * other.b,
                 self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        norm = other.a * other.a - 462 * other.b * other.b
        if not norm:
            raise ZeroDivisionError
        return self * K(other.a / norm, -other.b / norm)

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def sign(self):
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        comp = a * a - 462 * b * b
        return ((comp > 0) - (comp < 0)) * (1 if a > 0 else -1)

    def __eq__(self, other):
        try:
            other = self.cast(other)
        except (TypeError, ValueError):
            return False
        return self.a == other.a and self.b == other.b

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __float__(self):
        return float(self.a) + float(self.b) * 462**0.5

    def data(self):
        return [str(self.a), str(self.b)]


@lru_cache(None)
def matrix(word):
    a, b, c, d = 1, 0, 0, 1
    for v in word:
        a, b, c, d = b, a + v * b, d, c + v * d
    return a, b, c, d


def cf(word, tail):
    a, b, c, d = matrix(tuple(word))
    return (a * tail + b) / (c * tail + d)


@lru_cache(None)
def periodic(word):
    a, b, c, d = matrix(tuple(word))
    disc = (d - a)**2 + 4 * c * b
    factor = isqrt(disc // 462)
    assert 462 * factor * factor == disc, (word, disc)
    return K(Q(a - d, 2 * c), Q(factor, 2 * c))


@lru_cache(None)
def tail_endpoint(state, minimize):
    pre, period = extremal_tail(state, minimize)
    return cf(pre, periodic(period))


@lru_cache(None)
def side_endpoint(word, minimize):
    state = scan(word)
    if state is None:
        raise ValueError('Forbidden word')
    return cf(word, tail_endpoint(state, minimize == (len(word) % 2 == 0)))


@lru_cache(None)
def interval(a, b):
    return (side_endpoint(a, True) + side_endpoint(b, True),
            side_endpoint(a, False) + side_endpoint(b, False))


def denominators(word):
    _, _, c, d = matrix(tuple(word))
    return d, c


def parameters(a, b):
    qa, pa = denominators(a)
    qb, pb = denominators(b)
    return Q(pa, qa), Q(pb, qb), Q(qa * qa, qb * qb)


CF = K(Q(2221564096, 491993569), Q(283748, 491993569))


def union(intervals):
    result = []
    for lo, hi in sorted(intervals):
        assert lo <= hi
        if result and lo <= result[-1][1]:
            result[-1] = (result[-1][0], max(result[-1][1], hi))
        else:
            result.append((lo, hi))
    return result
