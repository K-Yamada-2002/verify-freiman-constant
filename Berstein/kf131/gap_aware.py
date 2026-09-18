"""Exclude a proved dead target range before committing to a successor.

This is a finite-horizon search constraint, not a recurrence proof.
The exclusion itself is independently certified by verify.py.
"""
from bisect import bisect_left, bisect_right
from fractions import Fraction as F
from exact import matrix
from search_types import Search, merge_float

GAP = (F('1.2924533'), F('1.2924537'))


class GapAwareSearch(Search):
    def _domain(self, u, v, depth):
        intervals = super()._domain(u, v, depth)
        if not depth or not (u.startswith('1122') and v.startswith('122')):
            return intervals
        _, bu, _, du = matrix(u)
        _, bv, _, dv = matrix(v)
        offset = F(bu, du)+F(bv, dv)
        lo, hi = [float((t-offset)*du*du) for t in GAP]
        pieces = []
        for a, b in intervals:
            if b < lo or hi < a:
                pieces.append((a, b))
            else:
                if a < lo:
                    pieces.append((a, lo))
                if hi < b:
                    pieces.append((hi, b))
        values = [x[0] for x in self.pool(u, v)]
        out = []
        for a, b in pieces:
            first, last = bisect_left(values, a), bisect_right(values, b)-1
            if first < last:
                out.append((values[first], values[last]))
        return tuple(merge_float(out))
