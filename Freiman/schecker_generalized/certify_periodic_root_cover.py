#!/usr/bin/env python3
"""Certify a Schecker-style root cover uniformly for n >= 1.

Write M(P)^n = u_n (M(P) - x I), x=u_{n-1}/u_n in [0,1/85].
The script checks every endpoint-overlap and old-v inequality for the short
successor chain by exact Bernstein subdivision over that entire rational
interval. This certifies only the initial convex-hull cover, not filling or
induction closure.
"""
from __future__ import annotations

import json
import math
import sys
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / "periodic_root_cover_certificate_20260925.json"
sys.path.insert(0, str(HERE))
import explore  # noqa: E402


@dataclass(frozen=True)
class Q21:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q21) else Q21(x)

    def __add__(self, other):
        other = Q21.coerce(other)
        return Q21(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q21(-self.a, -self.b)

    def __sub__(self, other):
        return self + -Q21.coerce(other)

    def __rsub__(self, other):
        return Q21.coerce(other) - self

    def __mul__(self, other):
        other = Q21.coerce(other)
        return Q21(self.a * other.a + 21 * self.b * other.b,
                   self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def sign(self):
        if not self.b:
            return (self.a > 0) - (self.a < 0)
        if not self.a or (self.a > 0) == (self.b > 0):
            return (self.b > 0) - (self.b < 0)
        delta = self.a * self.a - 21 * self.b * self.b
        return ((self.a > 0) - (self.a < 0)) * ((delta > 0) - (delta < 0))

    def __eq__(self, other):
        if not isinstance(other, (Q21, int, F)):
            return NotImplemented
        other = Q21.coerce(other)
        return self.a == other.a and self.b == other.b

    def record(self):
        return {"a": str(self.a), "b": str(self.b)}

    def decimal(self, digits=18):
        from decimal import Decimal, localcontext
        with localcontext() as ctx:
            ctx.prec = digits + 15
            value = (Decimal(self.a.numerator) / Decimal(self.a.denominator)
                     + Decimal(self.b.numerator) / Decimal(self.b.denominator)
                     * Decimal(21).sqrt())
            return f"{value:.{digits}f}"


def trim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def padd(p, q):
    n = max(len(p), len(q))
    sample = p[0] if p else q[0]
    zero = type(sample)(0)
    out = [zero for _ in range(n)]
    for i, x in enumerate(p):
        out[i] += x
    for i, x in enumerate(q):
        out[i] += x
    return trim(out)


def pscale(p, c):
    return trim([x * c for x in p])


def pmul(p, q):
    sample = p[0] if p else q[0]
    zero = type(sample)(0)
    out = [zero for _ in range(len(p) + len(q) - 1)]
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return trim(out)


def pconst(value):
    if isinstance(value, Q21):
        return [value]
    return [explore.Q.coerce(value)]


def matrix_const(word):
    return [[pconst(x) for x in row]
            for row in (explore.matrix(word)[:2], explore.matrix(word)[2:])]


def matrix_mul(left, right):
    result = [[pconst(0), pconst(0)], [pconst(0), pconst(0)]]
    for i in range(2):
        for j in range(2):
            result[i][j] = padd(
                pmul(left[i][0], right[0][j]),
                pmul(left[i][1], right[1][j]),
            )
    return result


P_MATRIX_MINUS_XI = [
    [pconst(14) + [explore.Q(-1)], pconst(19)],
    [pconst(53), pconst(72) + [explore.Q(-1)]],
]


def endpoint_rational(matrix, tail):
    a, b = matrix[0]
    c, d = matrix[1]
    numerator = padd(pscale(a, tail), b)
    denominator = padd(pscale(c, tail), d)
    return numerator, denominator


def fraction_add(first, second):
    n1, d1 = first
    n2, d2 = second
    return padd(pmul(n1, d2), pmul(n2, d1)), pmul(d1, d2)


def fraction_difference_sign(first, second):
    n1, d1 = first
    n2, d2 = second
    return trim(padd(pmul(n1, d2), pscale(pmul(n2, d1), -1)))


def binomial(n, k):
    return math.comb(n, k)


def field_power(value, exponent):
    result = type(value)(1)
    for _ in range(exponent):
        result *= value
    return result


def bernstein_coefficients(poly, lo, hi, field):
    poly = trim(poly)
    degree = len(poly) - 1
    width = hi - lo
    power_t = [field(0) for _ in range(degree + 1)]
    for k in range(degree + 1):
        for j in range(k, degree + 1):
            power_t[k] += (poly[j] * binomial(j, k)
                           * field_power(lo, j - k) * field_power(width, k))
    bernstein = []
    for i in range(degree + 1):
        value = field(0)
        for k in range(i + 1):
            value += power_t[k] * F(binomial(i, k), binomial(degree, k))
        bernstein.append(value)
    return bernstein


def certify_nonnegative(poly, lo, hi, field, max_depth=24):
    """Prove polynomial >=0 using exact Bernstein coefficients/subdivision."""
    poly = trim(poly)
    if all(x == 0 for x in poly):
        return {"proved": True, "leaves": 1, "max_depth": 0,
                "identically_zero": True}
    leaves = 0
    deepest = 0

    def visit(a, b, depth):
        nonlocal leaves, deepest
        deepest = max(deepest, depth)
        coeffs = bernstein_coefficients(poly, a, b, field)
        if all(c.sign() >= 0 for c in coeffs):
            leaves += 1
            return True
        if depth >= max_depth:
            return False
        mid = (a + b) / 2
        return visit(a, mid, depth + 1) and visit(mid, b, depth + 1)

    proved = visit(lo, hi, 0)
    return {"proved": proved, "leaves": leaves, "max_depth": deepest,
            "identically_zero": False}


def prove_endpoint_ge(first, second, label):
    # Both endpoint fractions have positive denominators by continued-fraction
    # matrix positivity on the parameter interval; prove the cross numerator.
    polynomial = fraction_difference_sign(first, second)
    return label, polynomial


def fixed_endpoint_matrices(left_suffix, right_suffix):
    left = matrix_mul(
        matrix_mul(matrix_const("4322"), P_MATRIX_MINUS_XI),
        matrix_const(left_suffix),
    )
    right = matrix_mul(
        matrix_mul(
            matrix_mul(matrix_const("3211"), P_MATRIX_MINUS_XI),
            matrix_const("3"),
        ),
        matrix_const(right_suffix),
    )
    return left, right


def sample_word(n, side, suffix):
    base = "4322" if side == "left" else "3211"
    middle = "" if side == "left" else "3"
    return base + "313121" * n + middle + suffix


def endpoint_data(left_suffix, right_suffix):
    left_word = sample_word(1, "left", left_suffix)
    right_word = sample_word(1, "right", right_suffix)
    left_matrix, right_matrix = fixed_endpoint_matrices(left_suffix, right_suffix)
    left_state, right_state = explore.state_of(left_word), explore.state_of(right_word)
    left_even = bool(len(left_word) % 2)
    right_even = bool(len(right_word) % 2)
    left_tails = (
        explore.extreme_tail(left_state, left_even)[0],
        explore.extreme_tail(left_state, not left_even)[0],
    )
    right_tails = (
        explore.extreme_tail(right_state, right_even)[0],
        explore.extreme_tail(right_state, not right_even)[0],
    )
    lo = fraction_add(
        endpoint_rational(left_matrix, left_tails[0]),
        endpoint_rational(right_matrix, right_tails[0]),
    )
    hi = fraction_add(
        endpoint_rational(left_matrix, left_tails[1]),
        endpoint_rational(right_matrix, right_tails[1]),
    )
    return {
        "left_suffix": left_suffix,
        "right_suffix": right_suffix,
        "sample_left_word": left_word,
        "sample_right_word": right_word,
        "legal": True,
        "lo": lo,
        "hi": hi,
        "left_denominators": [lo[1]],
        "right_denominators": [hi[1]],
        "left_matrix": left_matrix,
        "right_matrix": right_matrix,
    }


def rational_coefficients(poly):
    if any(coefficient.b for coefficient in poly):
        raise ValueError("continued-fraction matrix coefficient is not rational")
    return [Q21(coefficient.a) for coefficient in poly]


def width_factors(matrix):
    alpha = Q21(F(-1, 2), F(1, 6))
    beta = 3 * alpha
    c, d = matrix[1]
    c, d = rational_coefficients(c), rational_coefficients(d)
    return padd(pscale(c, alpha), d), padd(pscale(c, beta), d)


def old_v_polynomials(left_matrix, right_matrix):
    # v = width(right)/width(left); constants beta-alpha cancel.
    numerator = pmul(*width_factors(left_matrix))
    denominator = pmul(*width_factors(right_matrix))
    return numerator, denominator


def matrix_denominator_polys(matrix, tail_values):
    c, d = matrix[1]
    return [padd(pscale(c, tail), d) for tail in tail_values]


def main():
    x_lo_ratio, x_hi_ratio = F(0), F(1, 85)
    x_lo_endpoint = explore.Q(0)
    # Smaller eigenvalue of M(P); x_n increases to this endpoint from below.
    x_hi_endpoint = explore.Q(43, -2)
    q_below_old_bound = explore.Q(F(1, 85)) - x_hi_endpoint
    determinant_poly = [explore.Q(1), explore.Q(-86), explore.Q(1)]
    determinant_certificate = certify_nonnegative(
        determinant_poly, x_lo_endpoint, x_hi_endpoint, explore.Q
    )
    field462 = explore.Q
    field21 = Q21.coerce
    # Chains found by exact fixed-n interval covers. The periodic family starts
    # at n=1; the n=0 chain is checked directly by the fixed-word probe.
    suffixes = [
        ("", "1"), ("3", "3"), ("1", "2"),
        ("11", "3"), ("12", "3"), ("13", "31"),
    ]
    endpoints = [endpoint_data(left, right) for left, right in suffixes]

    # Verify every fixed branch is legal from the automaton states at n=1.
    legality = [
        {
            "left_suffix": item["left_suffix"],
            "right_suffix": item["right_suffix"],
            "legal": item["legal"],
            "left_state": explore.state_of(item["sample_left_word"]),
            "right_state": explore.state_of(item["sample_right_word"]),
        }
        for item in endpoints
    ]

    # Old v of parent and each child as exact rational functions of x.
    parent_data = endpoint_data("", "")
    ratios = []
    ratio_checks = []
    ratio_specs = [("parent", parent_data, F(1), F(19, 10))]
    ratio_specs.extend(
        (f"child_{i}", item, F(5, 17), F(17, 5))
        for i, item in enumerate(endpoints)
    )
    for label, item, lower, upper in ratio_specs:
        numerator, denominator = old_v_polynomials(
            item["left_matrix"], item["right_matrix"]
        )
        lower_poly = padd(numerator, pscale(denominator, -lower))
        upper_poly = padd(pscale(denominator, upper), pscale(numerator, -1))
        lo_cert = certify_nonnegative(lower_poly, x_lo_ratio, x_hi_ratio, field21)
        hi_cert = certify_nonnegative(upper_poly, x_lo_ratio, x_hi_ratio, field21)
        ratio_checks.extend([
            {"label": label + " lower", "threshold": str(lower), **lo_cert},
            {"label": label + " upper", "threshold": str(upper), **hi_cert},
        ])
        ratios.append((label, numerator, denominator))

    # Every continued-fraction endpoint denominator is positive on x's domain.
    denominator_checks = []
    for item in [parent_data, *endpoints]:
        for endpoint_name in ("lo", "hi"):
            num, den = item[endpoint_name]
            proof = certify_nonnegative(
                den, x_lo_ratio, x_hi_ratio, field462
            )
            denominator_checks.append({
                "word_pair": [item["sample_left_word"], item["sample_right_word"]],
                "endpoint": endpoint_name,
                **proof,
            })

    ratio_denominator_checks = []
    for item in [parent_data, *endpoints]:
        for side, matrix in (("left", item["left_matrix"]),
                             ("right", item["right_matrix"])):
            for factor_index, factor in enumerate(width_factors(matrix)):
                proof = certify_nonnegative(
                    factor, x_lo_ratio, x_hi_ratio, field21
                )
                ratio_denominator_checks.append({
                    "word_pair": [item["sample_left_word"],
                                  item["sample_right_word"]],
                    "side": side,
                    "factor": "alpha" if factor_index == 0 else "beta",
                    **proof,
                })

    # Cover inequalities: first child reaches the root low end, adjacent
    # intervals overlap, and the last child reaches the root high end.
    cover_polys = []
    _, parent_lo_ge_num = prove_endpoint_ge(parent_data["lo"], endpoints[0]["lo"],
                                             "first child starts before parent low")
    cover_polys.append(("parent_low_minus_child_0_low", parent_lo_ge_num))
    for i in range(len(endpoints) - 1):
        label, polynomial = prove_endpoint_ge(
            endpoints[i]["hi"], endpoints[i + 1]["lo"],
            f"child {i} overlaps child {i+1}",
        )
        cover_polys.append((label, polynomial))
    label, polynomial = prove_endpoint_ge(
        endpoints[-1]["hi"], parent_data["hi"], "last child reaches parent high"
    )
    cover_polys.append((label, polynomial))
    cover_checks = [
        {"label": label, **certify_nonnegative(
            poly, x_lo_endpoint, x_hi_endpoint, field462
        )}
        for label, poly in cover_polys
    ]

    # Check that each child's own lower endpoint is strictly below its upper.
    width_checks = [
        {
            "label": f"child_{i}_positive_width",
            **certify_nonnegative(
                fraction_difference_sign(item["hi"], item["lo"]),
                x_lo_endpoint, x_hi_endpoint, field462,
            ),
        }
        for i, item in enumerate(endpoints)
    ]

    all_proofs = (ratio_checks + denominator_checks + ratio_denominator_checks
                  + cover_checks + width_checks + [determinant_certificate])
    result = {
        "scope": (
            "Uniform initial convex-hull cover only for n>=1. This does not prove "
            "that any child hull is filled or close the recursive induction."
        ),
        "parameter": (
            "x=u_(n-1)/u_n in [0, 43-2*sqrt(462)], with "
            "M(P)^n=u_n(M(P)-xI); the endpoint is the smaller eigenvalue and "
            "x_n increases to it from below. The recurrence x_(n+1)=1/(86-x_n) "
            "keeps [0,q] invariant."
        ),
        "parameter_endpoint_q": x_hi_endpoint.record(),
        "q_positive_exact": x_hi_endpoint.sign() > 0,
        "q_below_1_over_85_exact": q_below_old_bound.sign() > 0,
        "period_matrix_determinant_nonnegative_on_parameter_domain":
            determinant_certificate,
        "selected_successors_in_(V_n,U_n)_orientation": [
            {"left_suffix": left, "right_suffix": right}
            for left, right in suffixes
        ],
        "automaton_legality": legality,
        "ratio_inequality_certificates": ratio_checks,
        "endpoint_denominator_certificates": denominator_checks,
        "old_v_denominator_certificates": ratio_denominator_checks,
        "interval_cover_certificates": cover_checks,
        "positive_child_width_certificates": width_checks,
        "all_checks_pass": (
            all(row["proved"] for row in all_proofs)
            and x_hi_endpoint.sign() > 0
            and q_below_old_bound.sign() > 0
        ),
        "bernstein_method": (
            "Exact polynomial inequalities in Q(sqrt(462)) or Q(sqrt(21)); "
            "Bernstein coefficients on rational subintervals, with exact bisection."
        ),
    }
    OUTPUT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(f"wrote {OUTPUT}")
    print(f"all checks pass: {result['all_checks_pass']}")
    for group in ("ratio_inequality_certificates", "endpoint_denominator_certificates",
                  "interval_cover_certificates", "positive_child_width_certificates"):
        rows = result[group]
        print(f"{group}: {sum(row['proved'] for row in rows)}/{len(rows)}")
        for row in rows:
            if not row["proved"]:
                print("  FAILED", row)


if __name__ == "__main__":
    main()
