"""Exact interval-type geometry normalized at alpha = sqrt(2)-1.

This module supplies comparisons and parameter transitions for a growing
interval-type graph. It does not assume that a candidate interval is filled.
"""
from dataclasses import dataclass
from functools import lru_cache, total_ordering

from exact import F, Q, matrix, state_of, extreme_tail, transform


@total_ordering
@dataclass(frozen=True)
class B:
    """a+b*sqrt(2), with a,b in Q(sqrt(10)); exact ordering in the real field."""
    a: Q = Q()
    b: Q = Q()

    def __post_init__(self):
        object.__setattr__(self, 'a', Q.coerce(self.a))
        object.__setattr__(self, 'b', Q.coerce(self.b))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, B) else B(value)

    def __add__(self, other):
        other = B.coerce(other)
        return B(self.a+other.a, self.b+other.b)
    __radd__ = __add__

    def __neg__(self):
        return B(-self.a, -self.b)

    def __sub__(self, other):
        return self+-B.coerce(other)

    def __rsub__(self, other):
        return B.coerce(other)+-self

    def __mul__(self, other):
        other = B.coerce(other)
        return B(self.a*other.a+2*self.b*other.b,
                 self.a*other.b+self.b*other.a)
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = B.coerce(other)
        norm = other.a*other.a-2*other.b*other.b
        if norm == 0:
            raise ZeroDivisionError
        return self*B(other.a/norm, -other.b/norm)

    def __rtruediv__(self, other):
        return B.coerce(other)/self

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise TypeError('integer exponents only')
        if exponent < 0:
            return (1/self)**(-exponent)
        out, base = B(1), self
        while exponent:
            if exponent % 2:
                out = out*base
            base = base*base
            exponent //= 2
        return out

    def sign(self):
        sa, sb = self.a.sign(), self.b.sign()
        if not sb:
            return sa
        if not sa or sa == sb:
            return sb
        return sa*(self.a*self.a-2*self.b*self.b).sign()

    def __eq__(self, other):
        if not isinstance(other, (B, Q, F, int)):
            return NotImplemented
        other = B.coerce(other)
        return self.a == other.a and self.b == other.b

    def __lt__(self, other):
        return (self-other).sign() < 0

    def decimal(self, digits=22):
        from decimal import Decimal, localcontext
        with localcontext() as ctx:
            ctx.prec = digits+40
            def rational(x):
                return Decimal(x.numerator)/Decimal(x.denominator)
            value = (rational(self.a.a)+rational(self.a.b)*Decimal(10).sqrt()
                     +(rational(self.b.a)+rational(self.b.b)*Decimal(10).sqrt())
                     * Decimal(2).sqrt())
            return f'{value:.{digits}f}'

    def record(self):
        return {'a': {'a': str(self.a.a), 'b': str(self.a.b)},
                'b': {'a': str(self.b.a), 'b': str(self.b.b)},
                'decimal': self.decimal()}


ALPHA = B(-1, 1)


def parameters(u, v):
    """r,s,h,relative parity; h is the derivative ratio AT ALPHA."""
    _, _, c, d = matrix(u)
    _, _, e, f = matrix(v)
    r, s = F(c, d), F(e, f)
    h = ((ALPHA*c+d)/(ALPHA*e+f))**2
    return r, s, h, (-1)**(len(u)+len(v))


def position(x, r):
    x, r = B.coerce(x), B.coerce(r)
    return (1+ALPHA*r)**2*x/(1+r*x)


@lru_cache(maxsize=65536)
def delta_range(x, y, rbox):
    """Exact extrema of A_r(x)-A_r(y) on a closed r interval.

    The derivative has at most one zero. Including this critical point
    avoids the incorrect assumption of monotonicity after normalization.
    """
    x, y = B.coerce(x), B.coerce(y)
    lo, hi = map(B.coerce, rbox)
    if not 0 <= lo <= hi or not 0 <= x <= 1 or not 0 <= y <= 1:
        raise ValueError('invalid shape box or tail endpoint')
    if x == y:
        return B(), B()
    candidates = [lo, hi]
    coefficient = ALPHA*(x+y)-2*x*y
    if coefficient != 0:
        critical = -(2*ALPHA-x-y)/coefficient
        if lo < critical < hi:
            candidates.append(critical)
    values = [(x-y)*(1+ALPHA*r)**2/((1+r*x)*(1+r*y)) for r in candidates]
    return min(values), max(values)


def difference_range(a, b, rbox, sbox, hbox, parity):
    """Extrema of F(a)-F(b) for F=A_r(x)+parity*h*A_s(y)."""
    if parity not in (-1, 1):
        raise ValueError('relative parity must be -1 or 1')
    h0, h1 = map(B.coerce, hbox)
    if not 0 < h0 <= h1:
        raise ValueError('positive derivative ratio required')
    dl = delta_range(a[0], b[0], rbox)
    dr = delta_range(a[1], b[1], sbox)
    if parity < 0:
        dr = -dr[1], -dr[0]
    products = [h*d for h in (h0, h1) for d in dr]
    return dl[0]+min(products), dl[1]+max(products)


def factor(word, r):
    """Square root of inverse derivative gain after appending word."""
    a, b, c, d = matrix(word)
    r = B.coerce(r)
    return (ALPHA*c+d+r*(ALPHA*a+b))/(1+r*ALPHA)


@lru_cache(maxsize=65536)
def factor_range(word, rbox):
    # This fractional linear function is monotone or constant.
    values = [factor(word, r) for r in rbox]
    return min(values), max(values)


@lru_cache(maxsize=65536)
def shape_image(word, rbox):
    a, b, c, d = matrix(word)
    values = [(B.coerce(r)*a+c)/(B.coerce(r)*b+d) for r in rbox]
    return min(values), max(values)


def transition(u, v, rbox, sbox, hbox, parity):
    """Enclose a whole child image, before any exchange of the two sides."""
    left, right = factor_range(u, rbox), factor_range(v, sbox)
    h0, h1 = map(B.coerce, hbox)
    return (shape_image(u, rbox), shape_image(v, sbox),
            (h0*(left[0]/right[1])**2, h1*(left[1]/right[0])**2),
            parity*(-1)**(len(u)+len(v)))


@lru_cache(maxsize=65536)
def tail_endpoint(state, word, high):
    if word.endswith('~2'):
        prefix = word[:-2]
        state_of(state+prefix+'2')
        return transform(prefix, ALPHA)
    if '#' in word:
        prefix, offset = word.split('#')
        end = state_of(state+prefix)
        value = ALPHA+F(offset)
        if not B(extreme_tail(end, False)[0]) <= value <= B(extreme_tail(end, True)[0]):
            raise ValueError('centered endpoint escapes tail hull')
        return transform(prefix, value)
    if '@' in word:
        prefix, weight = word.split('@')
        t = F(weight)
        if not 0 <= t <= 1:
            raise ValueError('interpolation weight must lie in [0,1]')
        end = state_of(state+prefix)
        a = extreme_tail(end, False)[0]
        b = extreme_tail(end, True)[0]
        return transform(prefix, (1-t)*a+t*b)
    end = state_of(state+word)
    return transform(word, extreme_tail(end, high)[0])


def endpoint_pair(states, label, suffixes=('', '')):
    u, high_u, v, high_v = label
    return (tail_endpoint(states[0], suffixes[0]+u, high_u),
            tail_endpoint(states[1], suffixes[1]+v, high_v))
