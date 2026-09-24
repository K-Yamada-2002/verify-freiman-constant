"""Correlated parameter domains: exact images of boxes under word pairs.

The outer box is a routing bound only. Comparisons are pulled back to the
base box, preserving all r/s/R correlations of the two word transforms.
"""
from dataclasses import dataclass
from functools import lru_cache

from explore import Q, matrix, state_of, transform
from type_graph_geometry import Cell, anchor, ge, require, square, swapped


def product(a, b):
    x, y, z, w = a
    e, f, g, h = b
    return x*e+y*g, x*f+y*h, z*e+w*g, z*f+w*h


def inverse(m):
    a, b, c, d = m
    determinant = a*d-b*c
    require(determinant in (-1, 1), 'non-unimodular word matrix')
    return d*determinant, -b*determinant, -c*determinant, a*determinant


@dataclass(frozen=True)
class Domain:
    base: Cell
    words: tuple = ('', '')
    high: bool = True

    @property
    def states(self):
        return tuple(state_of(s+w) for s, w in zip(self.base.states, self.words))

    @property
    def parity(self):
        return self.base.parity*(-1)**sum(map(len, self.words))

    @property
    def direction(self):
        return (-1)**len(self.words[0])

    def anchors(self):
        return anchor(self.states[0], self.high), anchor(self.states[1], self.high if self.parity > 0 else not self.high)

    @property
    def outer(self):
        return outer(self)

    @property
    def r(self):
        return self.outer.r

    @property
    def s(self):
        return self.outer.s

    @property
    def ratio(self):
        return self.outer.ratio

    def validate(self):
        self.base.validate()
        require(type(self.high) is bool and len(self.words) == 2, 'invalid chart orientation')
        require(all(isinstance(w, str) and all(d in '123' for d in w) for w in self.words), 'illegal chart word')
        self.states  # Checks the forbidden word, including the base state.
        self.outer.validate()
        return self

    def extend(self, u, v, high):
        require(bool(u or v) and all(c in '123' for c in u+v), 'empty or illegal successor')
        require(type(high) is bool, 'invalid successor anchor')
        return Domain(self.base, (self.words[0]+u, self.words[1]+v), high).validate()

    def exchange(self):
        return Domain(swapped(self.base), self.words[::-1],
                      self.high if self.parity > 0 else not self.high).validate()

    def record(self):
        return dict(base=self.base.record(), words=self.words, high=self.high)

    @classmethod
    def read(cls, data):
        if 'base' not in data:
            base = Cell.read(data)
            return cls(base, ('', ''), base.high).validate()
        return cls(Cell.read(data['base']), tuple(data['words']), data['high']).validate()


def matrix_image(base, matrices, target):
    """Outer box in target coordinates; None if a whole-box chart fails.

    Matrices may contain negative entries (inverse chart transitions).
    Denominators and derivative factors must stay nonzero. Their extrema
    are at endpoints because each factor is fractional linear.
    """
    shapes, factors = [], []
    for m, box, old_anchor, new_anchor in zip(matrices, (base.r, base.s), base.anchors(), target.anchors()):
        a, b, c, d = m
        denominators = [b*r+d for r in box]
        if denominators[0]*denominators[1] <= 0:
            return None
        values = [(a*r+c)/(b*r+d) for r in box]
        shape = min(values), max(values)
        if shape[0] < Q(1)/4 or shape[1] > 1:
            return None
        values = [(r*(a*new_anchor+b)+c*new_anchor+d)/(1+r*old_anchor) for r in box]
        if values[0]*values[1] <= 0:
            return None
        squares = list(map(square, values))
        shapes.append(shape)
        factors.append((min(squares), max(squares)))
    ratio = (base.ratio[0]*factors[0][0]/factors[1][1],
             base.ratio[1]*factors[0][1]/factors[1][0])
    return Cell(target.states, target.parity, target.high, *shapes, ratio).validate()


@lru_cache(maxsize=200000)
def outer(domain):
    # Only the orientation and anchors of target are used by matrix_image.
    target = Cell(domain.states, domain.parity, domain.high,
                  (Q(1)/4, Q(1)), (Q(1)/4, Q(1)), (Q(1), Q(1)))
    result = matrix_image(domain.base, tuple(map(matrix, domain.words)), target)
    require(result is not None, 'invalid forward parameter chart')
    return result


@lru_cache(maxsize=300000)
def relative_box(source, target):
    """Outer bound of target-chart inverse composed with the source chart.

    Equal words cancel exactly before interval evaluation. The result is
    an outer bound in target.base coordinates, not in the final coordinates.
    """
    if (source.states, source.parity, source.high) != (target.states, target.parity, target.high):
        return None
    matrices = tuple(product(matrix(s), inverse(matrix(t))) for s, t in zip(source.words, target.words))
    return matrix_image(source.base, matrices, target.base)


@lru_cache(maxsize=400000)
def compare(domain, a, b, strict=False):
    first = tuple(transform(w, x) for w, x in zip(domain.words, a))
    second = tuple(transform(w, x) for w, x in zip(domain.words, b))
    if domain.direction < 0:
        first, second = second, first
    return ge(domain.base, first, second, strict)
