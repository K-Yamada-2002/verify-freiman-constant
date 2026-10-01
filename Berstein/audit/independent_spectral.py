"""Independent rational audit of the below-ray spectral domination.

No imports from the construction or its verifiers.  All acceptance decisions
use Fraction, including the radical comparisons.  Seven-letter bulk windows
and every nearby center (including digits 1 and 2) are checked.  This proves
spectral domination only; the separate kernel audit proves interval filling.
"""

import argparse
import hashlib
import json
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path

BAD = (3, 1, 3, 1, 3)
LEFT, RIGHT = (3, 2, 2), (4, 3, 1)
TARGET = (F("4.52578"), F("4.52754"))
THETA = F("4.525423")


def allowed(word):
    return all(word[i : i + 5] != BAD for i in range(len(word) - 4))


def cf(word, tail):
    for digit in reversed(word):
        tail = 1 / (digit + tail)
    return tail


@lru_cache(None)
def extreme(history, minimum):
    """Enclose the extremal tail using 64 greedy digits and terminal [0,1].

    Every legal choice has an infinite continuation (append 2 forever).
    Continued fractions reverse lexicographic order at odd positions.
    Thus these 64 digits are those of the actual infinite extremum.
    """
    history = history[-4:]
    digits = []
    for index in range(64):
        choices = [d for d in (1, 2, 3) if allowed(history + (d,))]
        digit = (max if minimum == (index % 2 == 0) else min)(choices)
        digits.append(digit)
        history = (history + (digit,))[-4:]
    return tuple(sorted(cf(digits, t) for t in (F(0), F(1))))


def endpoint(prefix, outward_history, minimum):
    # For an odd prefix the decreasing map requires the opposite tail extreme.
    tail = extreme(outward_history[-4:], minimum != (len(prefix) % 2 == 1))
    return tuple(sorted(cf(prefix, t) for t in tail))


def upper(prefix, outward_history):
    return endpoint(prefix, outward_history, False)[1]


def radical_enclosure(a, b):
    scale = 10**70
    n = isqrt(462 * scale * scale)
    values = (a + b * F(n, scale), a + b * F(n + 1, scale))
    return min(values), max(values)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def convex(x, y, t):
    return ((1 - t) * x[0] + t * y[0], (1 - t) * x[1] + t * y[1])


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: this audit requires assertion checks")
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()

    bulk_max = F(0)
    bulk_witness = None
    bulk_count = 0
    for window in product((1, 2, 3), repeat=7):
        if not allowed(window):
            continue
        value = window[3] + upper(window[:3][::-1], window[::-1]) + upper(window[4:], window)
        bulk_count += 1
        if value > bulk_max:
            bulk_max, bulk_witness = value, window
    assert bulk_max < F("4.525091634")

    core = LEFT[::-1] + (4,) + RIGHT
    core_bounds = []
    for center in range(len(core)):
        if center == len(LEFT):
            continue
        value = core[center] + upper(core[:center][::-1], LEFT) + upper(core[center + 1 :], RIGHT)
        assert value < THETA
        core_bounds.append({"position": center - len(LEFT), "upper": str(value), "decimal": float(value)})

    near_count = 0
    near_max = F(0)
    near_witness = None
    for side, fixed, other in (("left", LEFT, RIGHT), ("right", RIGHT, LEFT)):
        prefixes = [()]
        for distance in range(1, 10):
            children = []
            for previous in prefixes:
                for digit in (1, 2, 3):
                    extension = previous + (digit,)
                    if not allowed(fixed + extension):
                        continue
                    children.append(extension)
                    toward_core = (fixed + previous)[::-1] + (4,) + other
                    value = digit + upper(toward_core, other) + upper((), fixed + extension)
                    assert value < THETA, (side, extension, value)
                    near_count += 1
                    if value > near_max:
                        near_max, near_witness = value, [side, distance, extension]
            prefixes = children

    # All remaining centers are >=10 digits beyond the fixed core. Replace
    # the backward digits after the first nine by 222..., keeping the outward
    # half unchanged. The resulting bilateral sequence is globally legal.
    # A nine-digit CF cylinder with terminal [0,1] has width
    # 1/(q_9*(q_9+q_8)) <= 1/55^2 (q_9 >= Fibonacci(10)=55).
    far_bound = bulk_max + F(1, 55**2)
    assert far_bound < THETA < TARGET[0]

    # Independently enclose both root extrema, using their original digits.
    hull = [add(endpoint(LEFT, LEFT, m), endpoint(RIGHT, RIGHT, m)) for m in (True, False)]
    stated_hull = [
        radical_enclosure(F(8512493, 17339617), F(28004, 17339617)),
        radical_enclosure(F(1352829, 2233974), F(-8081, 2233974)),
    ]
    # The exact symbolic equality is checked by independent_input.py. Here
    # both descriptions must agree in independently computed enclosures.
    for x, y in zip(hull, stated_hull):
        assert max(x[0], y[0]) <= min(x[1], y[1])
    low = convex(*hull, F(1, 16))
    high = convex(*hull, F(7, 8))
    low, high = (low[0] + 4, low[1] + 4), (high[0] + 4, high[1] + 4)
    freiman = radical_enclosure(F(2221564096, 491993569), F(283748, 491993569))
    assert THETA < low[0] <= low[1] < TARGET[0] < TARGET[1] < high[0] <= high[1] < freiman[0]

    # Controls based on false mathematical alternatives, not on output flags.
    central_lower = 4 + endpoint(LEFT, LEFT, False)[0] + endpoint(RIGHT, RIGHT, False)[0]
    assert central_lower > THETA  # The claimed bound really fails at the center.
    w = bulk_witness
    bulk_lower = w[3] + endpoint(w[:3][::-1], w[::-1], False)[0] + endpoint(w[4:], w, False)[0]
    assert bulk_lower > F("4.525")  # An overoptimistic bulk bound is false.
    assert high[1] < F("4.528")  # This larger requested endpoint is not covered.

    report = {
        "passed": True,
        "arithmetic": "stdlib Fraction only; no construction or verifier imports",
        "bulk_window_length": 7,
        "bulk_windows": bulk_count,
        "bulk_upper": str(bulk_max),
        "bulk_upper_decimal": float(bulk_max),
        "bulk_witness": bulk_witness,
        "core_bounds": core_bounds,
        "near_centers_checked": near_count,
        "near_upper": str(near_max),
        "near_upper_decimal": float(near_max),
        "near_witness": near_witness,
        "far_upper": str(far_bound),
        "far_upper_decimal": float(far_bound),
        "uniform_noncentral_upper": str(THETA),
        "root_interval_enclosures": [[str(z) for z in iv] for iv in (low, high)],
        "root_interval_decimals": [float(low[0]), float(high[1])],
        "rational_interval": [str(z) for z in TARGET],
        "negative_controls": 3,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("passed", "bulk_windows", "near_centers_checked", "far_upper_decimal", "root_interval_decimals", "negative_controls")}, indent=2))


if __name__ == "__main__":
    main()
