#!/usr/bin/env python3
"""Exact 131-free continued-fraction hulls in Q(sqrt(10)).

Arithmetic and automaton implementation adapted from
Freiman/schecker_generalized/explore.py. This is a separate model.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache, total_ordering
from itertools import product
from math import isqrt
import argparse
import json
from pathlib import Path


@total_ordering
@dataclass(frozen=True)
class Q:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q) else Q(x)

    def __add__(self, other):
        other = Q.coerce(other)
        return Q(self.a + other.a, self.b + other.b)
    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __sub__(self, other):
        return self + -Q.coerce(other)

    def __rsub__(self, other):
        return Q.coerce(other) - self

    def __mul__(self, other):
        other = Q.coerce(other)
        return Q(self.a * other.a + 10 * self.b * other.b,
                 self.a * other.b + self.b * other.a)
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Q.coerce(other)
        norm = other.a**2 - 10 * other.b**2
        if not norm:
            raise ZeroDivisionError
        return self * Q(other.a / norm, -other.b / norm)

    def __rtruediv__(self, other):
        return Q.coerce(other) / self

    def sign(self):
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a or (a > 0) == (b > 0):
            return (b > 0) - (b < 0)
        delta = a*a - 10*b*b
        return ((a > 0) - (a < 0)) * ((delta > 0) - (delta < 0))

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __eq__(self, other):
        if not isinstance(other, (Q, int, F)):
            return NotImplemented
        other = Q.coerce(other)
        return self.a == other.a and self.b == other.b

    def __abs__(self):
        return self if self.sign() >= 0 else -self

    def decimal(self, digits=22):
        # Display only; never used in a mathematical decision.
        from decimal import Decimal, localcontext
        with localcontext() as ctx:
            ctx.prec = digits + 20
            value = (Decimal(self.a.numerator) / Decimal(self.a.denominator)
                     + Decimal(self.b.numerator) / Decimal(self.b.denominator)
                     * Decimal(10).sqrt())
            return f'{value:.{digits}f}'

    def record(self):
        return {'a': str(self.a), 'b': str(self.b), 'decimal': self.decimal()}


BAN = '131'
STATES = ('', '1', '13')


def step(state, digit):
    candidate = state + digit
    if candidate.endswith(BAN):
        return None
    return max((s for s in STATES if candidate.endswith(s)), key=len)


def state_of(word):
    if any(a not in '123' for a in word):
        raise ValueError('prefix digits must belong to 1,2,3')
    state = ''
    for digit in word:
        state = step(state, digit)
        if state is None:
            raise ValueError(f'forbidden prefix {word}')
    return state


@lru_cache(None)
def matrix(word):
    a, b, c, d = 1, 0, 0, 1
    for digit in word:
        k = int(digit)
        a, b, c, d = b, a + k*b, d, c + k*d
    return a, b, c, d


def transform(word, x):
    a, b, c, d = matrix(word)
    return (a*x + b) / (c*x + d)


def periodic(period):
    a, b, c, d = matrix(period)
    disc = (d-a)**2 + 4*b*c
    square = isqrt(disc // 10)
    if 10*square*square != disc:
        raise ValueError('period endpoint outside Q(sqrt(10))')
    return Q(F(a-d, 2*c), F(square, 2*c))


@lru_cache(None)
def extreme_tail(state, maximize):
    seen, digits = {}, ''
    current = (state, maximize)
    while current not in seen:
        seen[current] = len(digits)
        s, high = current
        choices = [d for d in '123' if step(s, d) is not None]
        digit = min(choices) if high else max(choices)
        digits += digit
        current = (step(s, digit), not high)
    cut = seen[current]
    preperiod, period = digits[:cut], digits[cut:]
    value = transform(preperiod, periodic(period))
    return value, preperiod, period


@lru_cache(None)
def cylinder(word):
    state = state_of(word)
    low_tail, *_ = extreme_tail(state, bool(len(word) % 2))
    high_tail, *_ = extreme_tail(state, not bool(len(word) % 2))
    lo, hi = transform(word, low_tail), transform(word, high_tail)
    assert lo < hi
    return lo, hi


def hull(left, right):
    l, r = cylinder(left), cylinder(right)
    return l[0] + r[0], l[1] + r[1]


def merge(intervals):
    result = []
    for lo, hi in sorted(intervals):
        if result and lo <= result[-1][1]:
            result[-1] = (result[-1][0], max(hi, result[-1][1]))
        else:
            result.append((lo, hi))
    return result


@lru_cache(None)
def extensions(word, depth):
    if not depth:
        return (word,)
    return tuple(w + d for w in extensions(word, depth-1)
                 for d in '123' if step(state_of(w), d) is not None)

