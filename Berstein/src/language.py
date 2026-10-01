"""Fresh 131-avoidance automaton; no dependency on stashed work."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

DIGITS = (1, 2, 3)
BAD = (1, 3, 1)
STATES = tuple(BAD[:i] for i in range(len(BAD)))


def step(state, digit):
    word = state + (digit,)
    if word[-len(BAD):] == BAD:
        return None
    return max((s for s in STATES if not s or word[-len(s):] == s), key=len)


def scan(word):
    state = ()
    for digit in word:
        state = step(state, digit)
        if state is None:
            return None
    return state


@lru_cache(None)
def extremal_tail(state, minimize):
    # Alternating lexicographic order of continued fractions. Every allowed
    # digit has an infinite continuation (append 2 forever), so greedy is exact.
    seen, word, odd = {}, [], True
    while (state, odd) not in seen:
        seen[state, odd] = len(word)
        allowed = [d for d in DIGITS if step(state, d) is not None]
        digit = max(allowed) if minimize == odd else min(allowed)
        word.append(digit)
        state, odd = step(state, digit), not odd
    cut = seen[state, odd]
    return tuple(word[:cut]), tuple(word[cut:])

