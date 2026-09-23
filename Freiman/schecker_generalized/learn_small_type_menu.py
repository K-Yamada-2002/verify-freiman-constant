#!/usr/bin/env python3
"""Extract short endpoint templates and composed successors from prior graphs.

Input rules, including open graphs, are discovery data only. A composed word
is evaluated afresh on the original parent domain; intermediate box rounding
is not inherited. Exact verification of the output search remains mandatory.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

from explore import state_of
from type_graph_geometry import exchange, endpoint


def shape_key(shape):
    direct = tuple(sorted(map(tuple, shape)))
    reflected = tuple(sorted(exchange(z) for z in direct))
    return min(direct, reflected)


def template_labels(states, lower, upper, templates):
    """Keep a shared template's names when periodic tails have several names.

    Point-table deduplication is state-dependent and may otherwise print a
    different endpoint-word pair for the very same selected template.
    """
    for shape in templates:
        try:
            a, b = (endpoint(states, label) for label in shape)
        except ValueError:
            continue
        if (a, b) == (lower, upper):
            return tuple(map(tuple, shape))
        if (b, a) == (lower, upper):
            return tuple(map(tuple, shape[::-1]))
    raise ValueError('node endpoints do not belong to the declared template menu')


def compose(prefix, suffix, exchanged=False):
    """Suffix is written in the destination node's (possibly swapped) frame."""
    if exchanged:
        suffix = suffix[::-1]
    return tuple(a+b for a, b in zip(prefix, suffix))


def learn(graphs, depth=3, max_length=6, per_state=12, shape_count=12):
    shapes, moves, diagnostics = Counter(), defaultdict(Counter), []
    for data in graphs:
        nodes, cells = data['nodes'], data['cells']
        semantic = set()
        for i, node in enumerate(nodes):
            cell = cells[node['cell']]
            states = tuple(map(state_of, cell['states']))
            shape = shape_key((node['lower'], node['upper']))
            shapes[shape] += 1
            semantic.add((states, cell['parity'], cell['high'], shape))
            discovered = set()
            todo = [(i, ('', ''), False, 0)]
            while todo:
                j, prefix, swap, level = todo.pop()
                if level == depth:
                    continue
                for edge in nodes[j]['children']:
                    words = compose(prefix, tuple(edge['suffixes']), swap)
                    if sum(map(len, words)) > max_length:
                        continue
                    if level >= 1:
                        # Repeated ratio-bin destinations must not artificially
                        # multiply the frequency of an identical macro.
                        discovered.add(words)
                    for dest in edge['destinations']:
                        todo.append((dest['node'], words, swap ^ dest['swap'], level+1))
            for words in discovered:
                if any('31313' in s+w for s, w in zip(states, words)):
                    raise ValueError('composed successor crosses a forbidden word')
                moves[states, cell['parity']][words] += 1
        diagnostics.append(dict(nodes=len(nodes), parameter_cells=len(cells),
            endpoint_shapes=len({shape_key((n['lower'], n['upper'])) for n in nodes}),
            automaton_endpoint_types=len(semantic)))
    full = [shape_key((('', False, '', False), ('', True, '', True))),
            shape_key((('', False, '', True), ('', True, '', False)))]
    selected = list(dict.fromkeys(full+[s for s, _ in shapes.most_common(shape_count)]))[:max(2, shape_count)]
    return dict(format='freiman-small-menu-v1', diagnostics=diagnostics,
        settings=dict(depth=depth, max_length=max_length, per_state=per_state, shape_count=shape_count),
        shapes=[dict(endpoints=s, frequency=shapes[s]) for s in selected],
        macros=[dict(states=states, parity=p, successors=[dict(suffixes=w, frequency=n)
                 for w, n in sorted(counts.items(), key=lambda z: (-z[1], z[0]))[:per_state]])
                for (states, p), counts in sorted(moves.items())])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graphs', nargs='+', type=Path)
    ap.add_argument('--depth', type=int, default=3)
    ap.add_argument('--max-length', type=int, default=6)
    ap.add_argument('--per-state', type=int, default=12)
    ap.add_argument('--shape-count', type=int, default=12)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    if min(args.depth, args.max_length, args.per_state, args.shape_count) <= 0:
        ap.error('positive menu bounds required')
    result = learn([json.loads(p.read_text()) for p in args.graphs], args.depth,
                   args.max_length, args.per_state, args.shape_count)
    result['sources'] = [dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                         for p in args.graphs]
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(diagnostics=result['diagnostics'], shapes=len(result['shapes']),
                         macros=sum(len(r['successors']) for r in result['macros'])), indent=2))


if __name__ == '__main__':
    main()
