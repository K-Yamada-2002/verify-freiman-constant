#!/usr/bin/env python3
"""Uniform three-successor lemma extracted from the gap-aware search.

All comparisons use intervals in Q(sqrt(10)). This proves a local
numerical cover, not recurrence or filling of the child intervals.
"""
import json
from pathlib import Path
from exact import Q, F, state_of, extreme_tail, transform, matrix


def add(a, b): return (a[0]+b[0], a[1]+b[1])
def mul(a, b):
    z = [x*y for x in a for y in b]
    return min(z), max(z)
def div(a, b):
    assert b[0] > 0
    return mul(a, (1/b[1], 1/b[0]))
def point(x): return Q.coerce(x), Q.coerce(x)


def tail(word, high):
    return transform(word, extreme_tail(state_of(word), high)[0])


# An endpoint is (left suffix, high tail?, right suffix, high tail?).
# All suffixes here are relative to the ORIGINAL state-0 pair U,V.
ROOT = (('122', False, '13', True), ('211', False, '32', True))
CHILDREN = (
    (('122', False, '13', True), ('113', True, '32', False)),
    (('22', True, '132', False), ('31', False, '112', False)),
    (('222', False, '23', True), ('211', False, '32', True)),
)
PREFIXES = (('1', ''), ('', '1'), ('2', ''))


def endpoint_pair(label):
    u, h, v, k = label
    return tail(u, h), tail(v, k)


def difference(e1, e2, box):
    """E(e1)-E(e2), for BOTH original words odd.

    Cancel equal endpoints before enclosing. Differences of Mobius
    values are enclosed using the exact divided-difference identity.
    """
    x1, y1 = endpoint_pair(e1)
    x2, y2 = endpoint_pair(e2)
    r, s, q = box
    def delta(x, y, shape):
        if x == y: return point(0)
        den = mul(add(point(1), mul(shape, point(x))),
                  add(point(1), mul(shape, point(y))))
        return div(point(y-x), den)
    return add(delta(x1, x2, r), mul(q, delta(y1, y2, s)))


def compute():
    # Enlarge the shape box by making both boundary contacts identities.
    r = (Q(F(1, 4)), Q(F(4, 5)))
    s = (Q(F(1, 4)), Q(F(4, 5)))
    q = (Q(F(49, 100)), Q(F(53, 100)))
    box = (r, s, q)
    obligations = [
        ('root nondegenerate', ROOT[1], ROOT[0]),
        ('left boundary', ROOT[0], CHILDREN[0][0]),
        ('contact A-B', CHILDREN[0][1], CHILDREN[1][0]),
        ('contact B-C', CHILDREN[1][1], CHILDREN[2][0]),
        ('right boundary', CHILDREN[2][1], ROOT[1]),
    ]
    obligations += [(f'child {i} nondegenerate', hi, lo)
                    for i, (lo, hi) in enumerate(CHILDREN)]
    rows = []
    for name, e1, e2 in obligations:
        lo, hi = difference(e1, e2, box)
        assert lo >= 0, (name, lo.record())
        if 'nondegenerate' in name or 'contact' in name:
            assert lo > 0
        rows.append({'test': name, 'lower_bound': lo.record(), 'upper_bound': hi.record()})
    assert r[0] < F(2, 5) < r[1]
    assert s[0] < F(3, 7) < s[1]
    assert q[0] < F(25, 49) < q[1]
    return {'status': 'PROVED uniform local numerical cover; child recurrence UNPROVED',
            'root_states': ['empty', 'empty'], 'root_parities': ['odd', 'odd'],
            'box': {k: [z.record() for z in v] for k, v in zip(('r', 's', 'q'), box)},
            'root': ROOT, 'children_relative_to_root': CHILDREN,
            'child_prefixes': PREFIXES, 'checks': rows}


if __name__ == '__main__':
    result = compute()
    path = Path(__file__).with_name('uniform_cover.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
