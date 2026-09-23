#!/usr/bin/env python3
"""Fair, resumable semidecision search for finite Freiman chart proofs.

Each epoch advances the exhaustive certificate stream and one query of the
exact finite-library greatest fixed point. Every grammar/verifier operation
is finite. No heuristic can consume all future epochs or discard a universal
candidate. Completeness is relative to the existing certificate calculus and
unbounded continuation, not to mathematical truth or a finite wall-time limit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

from complete_certificate_codec import DecodeError, code_bits, decode_certificate
from complete_chart_library import ExactLibrary, FiniteClosure, build_bank
from verify_piecewise_charts import PiecewiseVerifier


def engine_hash():
    here = Path(__file__).parent
    names = ['search_complete_induction.py', 'complete_certificate_codec.py',
             'complete_chart_library.py', 'verify_piecewise_charts.py', 'verify_chart_types.py',
             'verify_cyclic_types.py', 'chart_geometry.py', 'type_graph_geometry.py',
             'explore.py', 'adaptive_types.py', 'uniform_initial_cover.py', 'contract_piecewise_charts.py']
    h = hashlib.sha256()
    for name in names:
        h.update(name.encode())
        h.update((here/name).read_bytes())
    return h.hexdigest()


def check_candidate(graph):
    return PiecewiseVerifier(graph).closed()


class ExhaustiveStream:
    def __init__(self, state=None, decoder=decode_certificate, checker=check_candidate):
        self.decoder, self.checker = decoder, checker
        next_code = 0 if state is None else int(state['next_code'])
        if next_code < 0:
            raise ValueError('invalid enumeration cursor')
        counts = dict(malformed=0, rejected=0, accepted=0) if state is None else dict(state['counts'])
        if sum(counts.values()) != next_code or counts['accepted']:
            raise ValueError('enumeration checkpoint skipped or double-counted candidates')
        self.record = (next_code, counts, None)

    @property
    def next_code(self):
        return self.record[0]

    @property
    def counts(self):
        return self.record[1]

    def step(self):
        graph, proof = None, None
        try:
            graph = self.decoder(code_bits(self.next_code))
        except DecodeError:
            status = 'malformed'
        else:
            try:
                proof = self.checker(graph)
            except (ValueError, ZeroDivisionError):
                status = 'rejected'
            else:
                status = 'accepted'
        # Unexpected errors, resource exhaustion or interruption leave the
        # cursor unchanged. A difficult candidate is never skipped forever.
        counts = dict(self.counts)
        counts[status] += 1
        winner = (graph, proof) if status == 'accepted' else None
        # One record replacement keeps cursor, counters and a found witness
        # together even if a signal arrives immediately after this assignment.
        self.record = self.next_code+1, counts, winner
        return winner

    def snapshot(self):
        return dict(next_code=str(self.next_code), counts=dict(self.counts))


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, separators=(',', ':'))+'\n')
    temporary.replace(path)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('graphs', nargs='*', type=Path)
    ap.add_argument('--resume', type=Path)
    ap.add_argument('--bank', type=Path)
    ap.add_argument('--seconds', type=float, default=180)
    ap.add_argument('--epochs', type=int, help='additional epochs; omission has no epoch cap')
    ap.add_argument('--fallback-batch', type=int, default=256)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.seconds <= 0 or args.fallback_batch <= 0 or (args.epochs is not None and args.epochs < 1):
        ap.error('positive resource limits required')
    if args.graphs and (args.resume or args.bank):
        ap.error('supply source graphs or a saved bank/state')
    version = engine_hash()
    previous = None
    if args.resume:
        previous = json.loads(args.resume.read_text())
        if previous['format'] != 'freiman-complete-search-state-v1' or previous['engine_hash'] != version:
            raise ValueError('state belongs to a different complete-search engine; do not skip old candidates')
        if previous.get('found'):
            raise ValueError('saved run already found a proof')
    bank_path = args.bank or (Path(previous['bank_path']) if previous else args.output.with_suffix('.bank.json'))
    if args.graphs:
        bank = build_bank([json.loads(p.read_text()) for p in args.graphs],
                          lambda row: print(json.dumps(row), flush=True))
        atomic_json(bank_path, bank)
    else:
        if not args.bank and previous is None:
            ap.error('source graphs, --bank or --resume required')
        bank = json.loads(bank_path.read_text())
    if previous is not None and bank['bank_hash'] != previous['bank_hash']:
        raise ValueError('state and finite candidate library do not match')
    library = ExactLibrary(bank)
    closure = FiniteClosure(len(library.checker.nodes), library.query,
                            None if previous is None else previous['closure'])
    stream = ExhaustiveStream(None if previous is None else previous['exhaustive'])
    epochs = 0 if previous is None else previous['epochs']
    started, first_epoch = time.monotonic(), epochs
    found, stop = None, 'time limit; search remains open'
    finite_audit = None if previous is None else previous.get('finite_audit')

    def save():
        state = dict(format='freiman-complete-search-state-v1', engine_hash=version,
                     bank_path=str(bank_path.resolve()), bank_hash=bank['bank_hash'],
                     closure=closure.snapshot(), exhaustive=stream.snapshot(), epochs=epochs,
                     finite_audit=finite_audit, found=found is not None)
        atomic_json(args.output.with_suffix('.state.json'), state)
        summary = dict(status='closed proof found' if found else 'no proof found; exhaustive search remains open',
                       stop=stop, epochs=epochs, epochs_this_run=epochs-first_epoch,
                       elapsed_search_seconds=time.monotonic()-started,
                       finite_library=library.outcome(closure), finite_scope=bank['scope'],
                       finite_audit=finite_audit,
                       exhaustive=stream.snapshot(), engine_hash=version, bank_hash=bank['bank_hash'],
                       relative_completeness='with unbounded continuation, every finite certificate in the grammar is eventually checked',
                       verification=None if found is None else found[1])
        atomic_json(args.output, summary)
        return summary

    last_save = started
    try:
        while time.monotonic()-started < args.seconds:
            if args.epochs is not None and epochs-first_epoch >= args.epochs:
                stop = 'epoch limit; search remains open'
                break
            for _ in range(args.fallback_batch):
                found = stream.step()
                if found:
                    break
            if found:
                stop = 'exhaustive stream found a closed proof'
                break
            if not closure.finished:
                closure.step()
            epochs += 1
            if closure.finished and finite_audit is None:
                finite_audit = library.verify_fixed_point(closure)
                print(json.dumps(dict(stage='finite library exhausted and replayed',
                                      result=library.outcome(closure), audit=finite_audit)), flush=True)
            if closure.finished and library.outcome(closure)['closed_in_this_menu']:
                found = library.certificate(closure)
                stop = 'exact finite-library solver found a closed proof'
                break
            if time.monotonic()-last_save >= 15:
                summary = save()
                print(json.dumps(dict(epochs=epochs, finite_library=summary['finite_library'],
                                      exhaustive=stream.snapshot())), flush=True)
                last_save = time.monotonic()
    except KeyboardInterrupt:
        stop = 'interrupted; enumeration cursor and unresolved queries retained'
    finally:
        if stream.record[2] is not None:
            found = stream.record[2]
        if found:
            # A final fresh replay gates the only success files.
            verification = check_candidate(found[0])
            atomic_json(args.output.with_suffix('.certificate.json'), found[0])
            atomic_json(args.output.with_suffix('.verified.json'), verification)
        else:
            args.output.with_suffix('.verified.json').unlink(missing_ok=True)
        print(json.dumps(save()), flush=True)


if __name__ == '__main__':
    main()
