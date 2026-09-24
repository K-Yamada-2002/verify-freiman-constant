#!/usr/bin/env python3
"""Exact obstruction to closing the six-offer recurrence, at every return.

The gap is in the UNION OF THE SIX SELECTED SUMS, not in K_F+K_F.
In fact, explicit cylinders of the parent sum lie inside this gap.
Discovery is unnecessary for replay: all comparisons are in Q(sqrt(10)).
"""
import argparse
from collections import deque
import json
from pathlib import Path

from exact import F, Q, hull, matrix, state_of, step
from child_recurrence import OFFERS, PREFIXES
from type_certificates import endpoint
from uniform_cover import ROOT, difference
from verify import children, exclusion


BASE = ('112', '122')
GAP_LABELS = (('11213', True, '11212', True),
              ('11213', False, '11213', False))
SEED_GAP = ('1.286107', '1.286110')
INITIAL_GAPS = (
    ('A1', 0, SEED_GAP),
    ('A2', 1, SEED_GAP),
    ('B1', 2, ('1.2922546', '1.2922552')),
    ('B2', 3, ('1.2922345', '1.2922353')),
    ('D1', 5, ('1.293763', '1.293765')),
)
SHAPE = (F(41420, 100000), F(41423, 100000))
RATIO = (F(49999, 100000), F(50001, 100000))
ENTRY = 4
MISSING = (('12', '2'), ('12', '3'))
OTHER_COMPLEMENT = (('13', '2'), ('13', '3'), ('3', '2'), ('3', '3'))
UNIFORM_WITNESS = ('123332', '213323')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parameters(u, v):
    _, _, c, d = matrix(u)
    _, _, e, f = matrix(v)
    return F(c, d), F(e, f), F(d*d, f*f)


def hull_label(u, v, high):
    """Suffix endpoint label for a hypothetical ODD/ODD state-0 parent."""
    return (u, bool(len(u) % 2) if high else not bool(len(u) % 2),
            v, bool(len(v) % 2) if high else not bool(len(v) % 2))


def walk_tree(nodes, root):
    """Check complete legal splits, allowing either side irrespective of width.

    This matters when reusing a tree on another shape: the side that was
    wider during discovery need not still be wider there.
    """
    require(bool(nodes), 'empty tree')
    require((nodes[0]['u'], nodes[0]['v']) == tuple(root), 'wrong root')
    seen = set()
    leaves = []

    def visit(i):
        require(type(i) is int and 0 <= i < len(nodes), 'invalid node index')
        require(i not in seen, 'cycle or shared tree node')
        seen.add(i)
        node = nodes[i]
        u, v = node['u'], node['v']
        state_of(u)
        state_of(v)
        if not node['children']:
            leaves.append(node)
            return
        for j in node['children']:
            require(type(j) is int and 0 <= j < len(nodes), 'invalid child index')
        actual = sorted((nodes[j]['u'], nodes[j]['v']) for j in node['children'])
        left = [(u+d, v) for d in '123' if step(state_of(u), d) is not None]
        right = [(u, v+d) for d in '123' if step(state_of(v), d) is not None]
        require(actual == left or actual == right, 'incomplete or illegal split')
        for j in node['children']:
            visit(j)

    visit(0)
    require(len(seen) == len(nodes), 'unreachable node')
    return leaves


def relative_tree(du, dv):
    target = tuple(map(F, SEED_GAP))
    nodes = exclusion(BASE[0]+du, BASE[1]+dv, target)
    result = []
    for n in nodes:
        item = {'u': n['u'][3:], 'v': n['v'][3:], 'children': n['children']}
        if not n['children']:
            lo, hi = hull(n['u'], n['v'])
            require(hi < target[0] or target[1] < lo, 'unresolved discovery leaf')
            item['side'] = 'below' if hi < target[0] else 'above'
        result.append(item)
    return result


def find_witness(u, v, target, budget=10000):
    """Find a whole nonempty cylinder sum strictly inside an open interval."""
    queue = deque([(u, v)])
    for _ in range(budget):
        require(bool(queue), 'no witness at this target')
        a, b = queue.popleft()
        lo, hi = hull(a, b)
        if hi <= target[0] or target[1] <= lo:
            continue
        if target[0] < lo and hi < target[1]:
            return a[len(u):], b[len(v):]
        queue.extend(children(a, b))
    raise ValueError('witness budget exhausted')


def comparisons(data):
    low, high = GAP_LABELS
    out = [('gap width', high, low, True),
           ('inside root lower', low, ROOT[0], True),
           ('inside root upper', ROOT[1], high, True)]
    require(len(data['relative_trees']) == len(PREFIXES), 'wrong forest size')
    for k, (nodes, prefix) in enumerate(zip(data['relative_trees'], PREFIXES)):
        for i, node in enumerate(walk_tree(nodes, prefix)):
            u, v = node['u'], node['v']
            if node['side'] == 'below':
                a, b = low, hull_label(u, v, True)
            else:
                require(node['side'] == 'above', 'invalid side')
                a, b = hull_label(u, v, False), high
            out.append((f'tree {k} leaf {i}', a, b, False))
    # These four missing rectangles also avoid the gap. The other two
    # are precisely the representations that must not be discarded.
    for u, v in OTHER_COMPLEMENT:
        if u == '13':
            a, b = low, hull_label(u, v, True)
        else:
            a, b = hull_label(u, v, False), high
        out.append((f'complement {u}|{v}', a, b, True))
    return out


def verify(data):
    """Replay the certificate; saved decimal values and reports are not trusted."""
    require(data['gap_labels'] == [list(e) for e in GAP_LABELS], 'wrong gap labels')
    require(data['shape_interval'] == list(map(str, SHAPE)), 'wrong shape domain')
    require(data['derivative_ratio_bounds'] == list(map(str, RATIO)), 'wrong ratio domain')
    require(data['entry_n'] == ENTRY, 'wrong entry index')
    require(tuple(data['uniform_witness']) == UNIFORM_WITNESS, 'wrong uniform witness')
    require(len(data['initial_obstructions']) == len(INITIAL_GAPS), 'missing initial check')
    initial_counts = {}
    for row, (name, k, target) in zip(data['initial_obstructions'], INITIAL_GAPS):
        require(row['name'] == name and row['target'] == list(target), 'wrong initial target')
        a, b = map(F, target)
        lo, hi = [endpoint(*BASE, e) for e in OFFERS[k]]
        require(lo < a < b < hi, 'target not inside the assigned offer')
        du, dv = PREFIXES[k]
        leaves = walk_tree(row['nodes'], (BASE[0]+du, BASE[1]+dv))
        for node in leaves:
            l, h = hull(node['u'], node['v'])
            require(h < a or b < l, 'initial exclusion failed')
        initial_counts[name] = {'nodes': len(row['nodes']), 'leaves': len(leaves)}

    # A symbolic partition of every possible first digit on each side,
    # further refining only the left digit 1. No numerical sampling.
    cells = [(u, v) for u in ('11', '12', '13', '2', '3') for v in '123']
    cover = PREFIXES + MISSING + OTHER_COMPLEMENT
    require(all(any(u.startswith(a) and v.startswith(b) for a, b in cover)
                for u, v in cells), 'incomplete parent partition')

    checks = comparisons(data)
    require(len(data['initial_witnesses']) == ENTRY, 'missing exceptional witness')
    summaries = []

    def evaluate(name, box, witness):
        u, v = witness
        state_of(u+'2')
        state_of(v+'2')
        rows = checks + [
            ('witness above lower gap end', hull_label(u, v, False), GAP_LABELS[0], True),
            ('witness below upper gap end', GAP_LABELS[1], hull_label(u, v, True), True),
        ]
        bounds = []
        for label, a, b, strict in rows:
            lo, hi = difference(a, b, box)
            require(lo > 0 if strict else lo >= 0, f'{name}: {label} failed')
            bounds.append({'test': label, 'strict': strict,
                           'lower': lo.record(), 'upper': hi.record()})
        summaries.append({'domain': name, 'checks': bounds})

    for n, witness in enumerate(data['initial_witnesses']):
        uv = tuple(w+'2'*n for w in BASE)
        r, s, q = parameters(*uv)
        evaluate(f'n={n}', tuple((Q(x), Q(x)) for x in (r, s, q)), witness)

    box = ((Q(SHAPE[0]), Q(SHAPE[1])),)*2 + ((Q(RATIO[0]), Q(RATIO[1])),)
    evaluate('invariant domain for every n >= 4', box, UNIFORM_WITNESS)

    # Invariance of r,s by 2, and entry at n=4. Invariance of H on [0,1]
    # is the chain-rule identity proved in SIX_OFFER_OBSTRUCTION.md.
    a, b = SHAPE
    require(a < 1/(2+b) <= 1/(2+a) < b, 'shape interval is not invariant')
    r, s, q = parameters(*(w+'2'*ENTRY for w in BASE))
    require(a < r < b and a < s < b, 'entry shapes outside domain')
    require(RATIO[0] < q < RATIO[1], 'entry H(0) outside domain')
    require(RATIO[0] < q*((1+r)/(1+s))**2 < RATIO[1], 'entry H(1) outside domain')

    # Endpoints really occur in the selected sums, so the open gap is
    # maximal, not merely an excluded subinterval of a larger gap.
    for e in GAP_LABELS:
        require(any(e[0].startswith(u) and e[2].startswith(v) for u, v in PREFIXES),
                'gap endpoint not in a selected cylinder')
        state_of(e[0])
        state_of(e[2])
    return {'initial_exclusions': initial_counts,
            'relative_tree_nodes': sum(map(len, data['relative_trees'])),
            'checked_parameter_domains': len(summaries),
            'bounds': summaries}


def compute():
    data = {
        'status': 'PROVED obstruction to six selected sums at every common-2 return; '
                  'NOT a gap in the parent sum and NOT an interior proof',
        'gap_labels': [list(e) for e in GAP_LABELS],
        'shape_interval': list(map(str, SHAPE)),
        'derivative_ratio_bounds': list(map(str, RATIO)),
        'entry_n': ENTRY,
        'relative_trees': [relative_tree(*p) for p in PREFIXES],
        'initial_obstructions': [
            {'name': name, 'target': list(target),
             'nodes': exclusion(BASE[0]+PREFIXES[k][0], BASE[1]+PREFIXES[k][1],
                                tuple(map(F, target)))}
            for name, k, target in INITIAL_GAPS
        ],
        'uniform_witness': list(UNIFORM_WITNESS),
        'initial_witnesses': [],
        'gap_examples': [],
    }
    for n in range(ENTRY+1):
        u, v = (w+'2'*n for w in BASE)
        target = sorted(endpoint(u, v, e) for e in GAP_LABELS)
        data['gap_examples'].append({'n': n, 'endpoints': [z.record() for z in target]})
        if n < ENTRY:
            data['initial_witnesses'].append(list(find_witness(u, v, target)))
    data['verification'] = verify(data)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--verify', type=Path, help='replay a saved certificate without discovery')
    args = parser.parse_args()
    if args.verify:
        data = json.loads(args.verify.read_text())
        result = verify(data)
    else:
        data = compute()
        args.output.write_text(json.dumps(data, indent=2)+'\n')
        result = data['verification']
    print(json.dumps({k: v for k, v in result.items() if k != 'bounds'}, indent=2))
    print('The six-offer obstruction is proved at all returns. Interior remains unproved.')


if __name__ == '__main__':
    main()
