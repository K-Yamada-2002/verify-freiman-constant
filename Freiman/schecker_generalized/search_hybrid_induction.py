#!/usr/bin/env python3
"""Useful search with a positive, independent exhaustive time allocation.

Every epoch gives the universal stream at least one candidate and a small
time slice. Heuristics cannot mark its candidates rejected. A finite accepted
certificate is therefore eventually found under unbounded continuation.
The configured time share is approximate: an indivisible query may overrun.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

from hybrid_discovery import Constructive, Mosaic
from reduce_chart_frontier import counts
from search_complete_induction import ExhaustiveStream, atomic_json, check_candidate, engine_hash
from search_piecewise_charts import fingerprint
from verify_piecewise_charts import PiecewiseVerifier


def discovery_hash():
    here = Path(__file__).parent
    return hashlib.sha256(fingerprint().encode() + (here/'hybrid_discovery.py').read_bytes()
                          + (here/'search_hybrid_induction.py').read_bytes()).hexdigest()


class FairSlices:
    """Positive universal quota before every finite discovery slice."""
    def __init__(self, stream, fast_step, share=.05, quantum=1., clock=time.monotonic):
        if not 0 < share < 1 or not quantum > 0:
            raise ValueError('positive shares and quantum required')
        self.stream, self.fast_step = stream, fast_step
        self.share, self.quantum, self.clock = share, quantum, clock
        self.seconds = dict(exhaustive=0., discovery=0.)

    def epoch(self):
        start = self.clock()
        while True:
            winner = self.stream.step()
            if winner or self.clock()-start >= self.share*self.quantum:
                break
        self.seconds['exhaustive'] += self.clock()-start
        if winner:
            return winner
        start = self.clock()
        while True:
            winner = self.fast_step()
            if winner or self.clock()-start >= (1-self.share)*self.quantum:
                break
        self.seconds['discovery'] += self.clock()-start
        return winner


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--graph', type=Path)
    ap.add_argument('--search-state', type=Path)
    ap.add_argument('--complete-state', type=Path)
    ap.add_argument('--resume', type=Path)
    ap.add_argument('--seconds', type=float, default=180)
    ap.add_argument('--epochs', type=int)
    ap.add_argument('--fallback-share', type=float, default=.05)
    ap.add_argument('--quantum', type=float, default=1.)
    ap.add_argument('--synthesis-share', type=float, default=.2,
                    help='approximate fraction of discovery time spent on new-type synthesis')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not (args.seconds > 0 and 0 < args.fallback_share < 1 and args.quantum > 0
            and 0 < args.synthesis_share < 1 and (args.epochs is None or args.epochs > 0)):
        ap.error('invalid positive budgets')
    if args.resume and (args.graph or args.search_state or args.complete_state):
        ap.error('--resume cannot be combined with seed files')
    if not args.resume and not (args.graph and args.search_state):
        ap.error('--graph and --search-state required for a new run')
    language, discovery = engine_hash(), discovery_hash()
    if args.resume:
        previous = json.loads(args.resume.read_text())
        if previous['format'] != 'freiman-hybrid-search-state-v1' or previous['language_hash'] != language:
            raise ValueError('universal language changed; its old cursor must not skip changed candidates')
        if previous['discovery_hash'] != discovery or previous['found']:
            raise ValueError('incompatible discovery checkpoint or already completed run')
        stream = ExhaustiveStream(previous['exhaustive'])
        mosaic = Mosaic(state=previous['mosaic'])
        synthesis = Constructive(state=previous['synthesis'])
        epochs, lane_seconds = previous['epochs'], previous['lane_seconds']
    else:
        universal = None
        if args.complete_state:
            previous = json.loads(args.complete_state.read_text())
            if previous.get('language_hash', previous.get('engine_hash')) != language or previous.get('found'):
                raise ValueError('incompatible universal cursor')
            universal = previous['exhaustive']
        stream = ExhaustiveStream(universal)
        mosaic = Mosaic(json.loads(args.graph.read_text()))
        synthesis = Constructive(json.loads(args.search_state.read_text()))
        epochs, lane_seconds = 0, dict(mosaic=0., synthesis=0.)
    baseline = dict(mosaic=counts(mosaic.graph), synthesis=synthesis.game.summary())
    initial_cursor, first_epoch = stream.next_code, epochs
    start = last_save = time.monotonic()
    found, stop = None, 'time budget; all remaining obligations retained'

    def fast_step():
        nonlocal found
        total = sum(lane_seconds.values())
        choose_synthesis = mosaic.finished or lane_seconds['synthesis'] < total*args.synthesis_share
        lane = 'synthesis' if choose_synthesis else 'mosaic'
        before = time.monotonic()
        if choose_synthesis:
            synthesis.step()
            if synthesis.game.closed():
                graph = synthesis.graph()
                found = graph, check_candidate(graph)
        else:
            mosaic.step()
            if mosaic.statistics['accepted'] == len(mosaic.targets):
                found = mosaic.graph, check_candidate(mosaic.graph)
        lane_seconds[lane] += time.monotonic()-before
        return found

    scheduler = FairSlices(stream, fast_step, args.fallback_share, args.quantum)

    def save():
        atomic_json(args.output.with_suffix('.state.json'),
                    dict(format='freiman-hybrid-search-state-v1', language_hash=language,
                         discovery_hash=discovery, exhaustive=stream.snapshot(), epochs=epochs,
                         mosaic=mosaic.snapshot(), synthesis=synthesis.snapshot(),
                         lane_seconds=lane_seconds, found=found is not None))
        summary = dict(status='closed proof found' if found else 'induction remains open',
                       stop=stop, epochs=epochs, epochs_this_run=epochs-first_epoch,
                       elapsed_search_seconds=time.monotonic()-start,
                       universal_candidates_this_run=stream.next_code-initial_cursor,
                       exhaustive=stream.snapshot(), lane_seconds=lane_seconds,
                       scheduler_seconds_this_run=scheduler.seconds,
                       requested_fallback_share=args.fallback_share,
                       share_semantics='time slices; one finite query may overrun; no worst-case speed bound',
                       baseline=baseline,
                       mosaic=dict(counts=counts(mosaic.graph), statistics=mosaic.statistics,
                                   processed_targets=mosaic.position, total_targets=len(mosaic.targets),
                                   finished=mosaic.finished),
                       synthesis=dict(summary=synthesis.game.summary(), statistics=synthesis.statistics,
                                      round=synthesis.round),
                       language_hash=language, discovery_hash=discovery,
                       relative_completeness='every finite certificate accepted by the current verifier is eventually tested under unbounded continuation',
                       verification=None if found is None else found[1])
        atomic_json(args.output, summary)
        return summary

    save()  # A durable discovery checkpoint exists even before the first query.
    try:
        while time.monotonic()-start < args.seconds:
            if args.epochs is not None and epochs-first_epoch >= args.epochs:
                stop = 'epoch budget; search remains open'
                break
            found = scheduler.epoch()
            epochs += 1
            if found:
                stop = 'fresh exact closed-certificate verification succeeded'
                break
            if time.monotonic()-last_save >= 15:
                summary = save()
                print(json.dumps({k: summary[k] for k in ('epochs', 'mosaic', 'synthesis', 'universal_candidates_this_run')}), flush=True)
                last_save = time.monotonic()
    except KeyboardInterrupt:
        # Keep the last durable discovery state if interrupted in a mutable
        # discovery operation; never persist an incompletely installed rule.
        # Universal checks commit atomically and have an independent snapshot.
        atomic_json(args.output.with_suffix('.cursor.json'),
                    dict(language_hash=language, exhaustive=stream.snapshot(),
                         winner=stream.record[2]))
        if stream.record[2] is not None:
            atomic_json(args.output.with_suffix('.certificate.json'), stream.record[2][0])
            atomic_json(args.output.with_suffix('.verified.json'), check_candidate(stream.record[2][0]))
        raise
    finally:
        synthesis.search.close_native()
    if stream.record[2] is not None:
        found = stream.record[2]
    if found:
        atomic_json(args.output.with_suffix('.certificate.json'), found[0])
        atomic_json(args.output.with_suffix('.verified.json'), check_candidate(found[0]))
    else:
        args.output.with_suffix('.verified.json').unlink(missing_ok=True)
    for lane, graph in (('mosaic', mosaic.graph), ('synthesis', synthesis.graph())):
        audit = PiecewiseVerifier(graph).audit()
        if audit['failed_rules']:
            raise ValueError('discovery output failed independent exact audit')
        atomic_json(args.output.with_suffix('.'+lane+'.json'), graph)
        atomic_json(args.output.with_suffix('.'+lane+'.audit.json'), audit)
    print(json.dumps(save()), flush=True)


if __name__ == '__main__':
    main()
