#!/usr/bin/env python3
"""Repair an audited partial induction instead of restarting from its roots."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from search_cyclic_types import Search
from type_graph_geometry import full_labels
from verify_cyclic_types import Verifier


def graph_labels(data):
    return [tuple(row[k]) for n in data['nodes'] for row in [n]+n.get('children', [])
            for k in ('lower', 'upper')]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graph', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--native-executable', type=Path)
    ap.add_argument('--seconds', type=float, default=240)
    ap.add_argument('--max-steps', type=int, default=100000)
    ap.add_argument('--max-types', type=int, default=20000)
    ap.add_argument('--max-shapes', type=int, default=64)
    ap.add_argument('--outer-depth', type=int, default=4)
    ap.add_argument('--outer-samples', type=int, choices=(1, 3, 9), default=9)
    ap.add_argument('--max-step', type=int, default=1)
    ap.add_argument('--depth-first', action='store_true')
    ap.add_argument('--min-cost-cover', action='store_true')
    ap.add_argument('--unrestricted-shapes', action='store_true')
    ap.add_argument('--no-prefilter', action='store_true')
    ap.add_argument('--gap-endpoints', type=Path, nargs='*', default=[],
                    help='additional candidate endpoints learned from exact gap certificates')
    args = ap.parse_args()
    if min(args.seconds, args.max_steps, args.max_types, args.max_step, args.max_shapes) <= 0:
        ap.error('search bounds must be positive')
    data = json.loads(args.graph.read_text())
    source_hash = Verifier(data).proof_hash()
    bank = json.loads(Path(__file__).with_name('adaptive_depth8_certificate.json').read_text())
    labels = graph_labels(data)+[tuple(z) for case in bank['cases'] for shape in case['types'] for z in shape]
    gap_sources = []
    for path in args.gap_endpoints:
        gaps = json.loads(path.read_text())
        gap_sources.append(gaps['source_proof_hash'])
        labels.extend(tuple(w['boundary_labels'][side]) for w in gaps['witnesses']
                      if 'boundary_labels' in w for side in ('lower', 'upper'))
    menu = None if args.unrestricted_shapes else data.get('shape_menu') or [full_labels(1), full_labels(-1)]
    settings = data.get('settings', {})
    search = Search(labels, states=int(settings.get('states', 6)), bins=int(settings.get('bins', 25)),
                    base=F(settings.get('base', '22/25')), max_step=args.max_step,
                    outer_depth=args.outer_depth, outer_samples=args.outer_samples, local_filter=False,
                    balance=F(9, 10), reuse_pending=True, shape_menu=menu, adaptive_shapes=True,
                    max_shapes=args.max_shapes, min_cost_cover=args.min_cost_cover)
    if args.native_executable:
        search.native_executable = args.native_executable.resolve()
    game = search.import_certificate(data, depth_first=args.depth_first)
    initial = game.summary()
    rejected = []
    if not args.no_prefilter:
        for i, key in enumerate(game.keys):
            if not search.outer_possible(key):
                rejected.append(i)
        for i in rejected:
            game.reject(game.keys[i], permanent=True)
    print(json.dumps(dict(imported=initial, prefilter_rejected=len(rejected))), flush=True)

    def checkpoint(game):
        cert = search.certificate(game)
        cert['shape_menu'] = search.shape_menu
        cert['shape_learning'] = search.shape_learning
        cert['settings'] = dict(settings, outer_depth=args.outer_depth, outer_samples=args.outer_samples,
                                max_step=args.max_step)
        cert['resume'] = dict(source_proof_hash=source_hash, initial=initial,
                              gap_endpoint_sources=gap_sources,
                              prefilter_rejected=rejected,
                              settings={k: str(v) if isinstance(v, Path) else
                                        list(map(str, v)) if isinstance(v, list) else v
                                        for k,v in vars(args).items()})
        cert['search']['closed_supported_types'] = len(game.supported())
        cert['search']['permanent_filter_rejections'] = len(game.permanent_rejections)
        tmp = args.output.with_suffix('.tmp')
        tmp.write_text(json.dumps(cert, indent=2)+'\n')
        tmp.replace(args.output)
        print(json.dumps(game.summary()), flush=True)

    checkpoint(game)
    try:
        game.run(search.planner, args.max_types, args.max_steps, args.seconds, checkpoint)
    except KeyboardInterrupt:
        game.stop = 'interrupted; remaining obligations preserved'
    finally:
        search.close_native()
    checkpoint(game)
    checker = Verifier(json.loads(args.output.read_text()))
    audit = checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit, indent=2)+'\n')
    print(json.dumps(dict(local=len(audit['verified_rules']), open=len(audit['open_nodes']),
                          failed=len(audit['failed_rules']))), flush=True)
    try:
        verified = checker.closed()
    except ValueError as error:
        print(json.dumps(dict(closed=False, reason=str(error))), flush=True)
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(verified, indent=2)+'\n')
        print(json.dumps(verified), flush=True)


if __name__ == '__main__':
    main()
