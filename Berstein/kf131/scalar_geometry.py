"""Exact centered coordinates and affine transports for scalar interval types.

G(x,y) = A_r(x)-A_r(alpha) + p*h*(A_s(y)-A_s(alpha)).
A child scalar interval has a parameter-dependent affine image in G.
"""
from functools import lru_cache

from exact import matrix, transform
from anchored_geometry import ALPHA, B


@lru_cache(maxsize=65536)
def quadratic_parameters(word,rbox):
    _,_,c,d=matrix(word)
    z,denominator=transform(word,ALPHA),c*ALPHA+d
    lo,hi=map(B.coerce,rbox)
    if not 0 <= lo <= hi:
        raise ValueError('invalid shape interval')
    ts=tuple(sorted((1+r*ALPHA)/(1+r*z) for r in (lo,hi)))
    return z-ALPHA,1/(denominator**2),ts


@lru_cache(maxsize=131072)
def quadratic_range(word, coefficient, rbox):
    """Exact range of c_word(r) + coefficient / f_word(r)^2.

Write z=phi_word(alpha), D=c*alpha+d, t=(1+r*alpha)/(1+r*z).
The expression is (z-alpha)*t + coefficient*t^2/D^2. The map r -> t
is monotone, so two endpoints and at most one quadratic vertex suffice.
    """
    b,inverse_square,ts=quadratic_parameters(word,rbox)
    a=B.coerce(coefficient)*inverse_square
    candidates = list(ts)
    # The derivative is affine; only divide when its zero lies strictly
    # between the endpoints. This is the same exact extremum test.
    if a != 0 and (2*a*ts[0]+b)*(2*a*ts[1]+b)<0:
        critical = -b/(2*a)
        candidates.append(critical)
    values = [(a*t+b)*t for t in candidates]
    return min(values), max(values)


def endpoint_image(u, v, swap, endpoint, rbox, sbox, hbox, parity):
    """Exact range of a child scalar endpoint in parent coordinates.

The formula is valid on the full parent box. For a swap case used only
on part of that box, these bounds remain conservative.
    """
    if type(swap) is not bool or parity not in (-1, 1):
        raise ValueError('invalid swap or parity')
    left = quadratic_range(u, 0 if swap else (-1)**len(u)*endpoint, tuple(rbox))
    right = quadratic_range(v, (-1)**len(v)*endpoint if swap else 0, tuple(sbox))
    if parity < 0:
        right = -right[1], -right[0]
    h0, h1 = map(B.coerce, hbox)
    if not 0 < h0 <= h1:
        raise ValueError('invalid ratio interval')
    products = [h*r for h in (h0, h1) for r in right]
    return left[0]+min(products), left[1]+max(products)


def uniform_child_core(u, v, swap, interval, rbox, sbox, hbox, parity):
    """Largest constant interval certified by these endpoint range bounds."""
    lo, hi = interval
    if not lo < hi:
        raise ValueError('child interval must have positive width')
    sign = parity*(-1)**len(v) if swap else (-1)**len(u)
    a, b = (lo, hi) if sign > 0 else (hi, lo)
    left = endpoint_image(u, v, swap, a, rbox, sbox, hbox, parity)
    right = endpoint_image(u, v, swap, b, rbox, sbox, hbox, parity)
    return left[1], right[0]
