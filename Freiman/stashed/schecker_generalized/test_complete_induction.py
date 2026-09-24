import copy
from fractions import Fraction
import itertools
import json
import random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from complete_certificate_codec import (DecodeError, Reader, Writer, bits_code, code_bits,
                                        code_word, decode_certificate, encode_certificate, word_code)
from complete_chart_library import ExactLibrary, FiniteClosure, build_bank
from explore import Q
from search_complete_induction import ExhaustiveStream
from test_piecewise_charts import split_rule
from verify_piecewise_charts import PiecewiseVerifier


def solve_options(options, pause=None):
    def oracle(i, alive):
        for index, children in enumerate(options[i]):
            if children <= alive:
                return dict(payload=index, dependencies=sorted(children))
        return None
    solver = FiniteClosure(len(options), oracle)
    while solver.step():
        if pause is not None and solver.steps == pause:
            solver = FiniteClosure(len(options), oracle, json.loads(json.dumps(solver.snapshot())))
            pause = None
    return solver


class CompleteInductionTests(unittest.TestCase):
    def test_finite_closure_equals_union_of_all_closed_subsets(self):
        rng = random.Random(462)
        for _ in range(80):
            n = 7
            options = [[set(rng.sample(range(n), rng.randrange(4))) for _ in range(rng.randrange(4))]
                       for _ in range(n)]
            expected = set()
            for mask in range(1 << n):
                subset = {i for i in range(n) if mask & (1 << i)}
                if all(any(c <= subset for c in options[i]) for i in subset):
                    expected |= subset
            solver = solve_options(options)
            self.assertEqual(solver.alive, expected)
            self.assertEqual(solve_options(options, pause=3).snapshot(), solver.snapshot())

    def test_alternative_replaces_dead_first_choice_and_keeps_mutual_cycle(self):
        solver = solve_options([[{2}, {1}], [{0}], []])
        self.assertEqual(solver.alive, {0, 1})
        self.assertEqual(solver.plans[0]['dependencies'], [1])
        self.assertGreater(solver.steps, 3)

    def test_interrupted_commit_requeues_every_surviving_type(self):
        solver = FiniteClosure(3, lambda i, a: None)
        solver.step()
        solver.dirty = True
        solver.queue.clear()
        snapshot = solver.snapshot()
        self.assertFalse(solver.finished)
        self.assertEqual(snapshot['alive'], [1, 2])
        self.assertEqual(snapshot['queue'], [1, 2])

    def test_integer_and_word_codes_are_exhaustive_bijections(self):
        previous = []
        for n in range(2000):
            bits = code_bits(n)
            self.assertEqual(bits_code(bits), n)
            self.assertEqual(word_code(code_word(n)), n)
            writer = Writer()
            writer.uint(n)
            self.assertEqual(Reader(''.join(writer.parts)).uint(), n)
            previous.append(bits)
        self.assertEqual(previous[:7], ['', '0', '1', '00', '01', '10', '11'])

    def test_large_rationals_and_interpolated_endpoints_roundtrip(self):
        writer = Writer()
        values = [Fraction(0), Fraction(-3, 7), Fraction(2**170+3, 5**90)]
        for value in values:
            writer.rational(value)
        label = ['123@2/7', True, '@1/3', False]
        writer.label(label)
        reader = Reader(''.join(writer.parts))
        self.assertEqual([Fraction(reader.rational()) for _ in values], values)
        self.assertEqual(reader.label(), label)
        self.assertEqual(reader.position, len(reader.bits))

    def test_real_guarded_certificate_roundtrip_and_exact_rejection(self):
        data, _, _ = split_rule()
        bits = encode_certificate(data)
        decoded = decode_certificate(bits)
        self.assertEqual(encode_certificate(decoded), bits)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in verification')):
            audit = PiecewiseVerifier(decoded).audit()
            self.assertFalse(audit['failed_rules'])
            self.assertTrue(audit['open_nodes'])
            with self.assertRaisesRegex(ValueError, 'unresolved'):
                PiecewiseVerifier(decoded).closed()
        with self.assertRaises(DecodeError):
            decode_certificate(bits+'0')
        with self.assertRaises(DecodeError):
            decode_certificate(bits[:-1])

    def test_malformed_codes_are_finite_and_do_not_crash_decoder(self):
        for n in range(4096):
            try:
                decode_certificate(code_bits(n))
            except DecodeError:
                pass

    def test_exhaustive_cursor_resume_reaches_late_witness_without_skipping(self):
        visited = []
        def decode(bits):
            index = bits_code(bits)
            visited.append(index)
            if index % 3 == 0:
                raise DecodeError('invalid grammar example')
            return index
        def check(index):
            if index != 83:
                raise ValueError('not a proof')
            return dict(proof=index)
        stream = ExhaustiveStream(decoder=decode, checker=check)
        for _ in range(37):
            self.assertIsNone(stream.step())
        stream = ExhaustiveStream(json.loads(json.dumps(stream.snapshot())), decode, check)
        winner = None
        while winner is None:
            winner = stream.step()
        self.assertEqual(visited, list(range(84)))
        self.assertEqual(winner, (83, dict(proof=83)))
        self.assertEqual(stream.counts['accepted'], 1)

    def test_resource_failure_does_not_advance_the_enumeration_cursor(self):
        stream = ExhaustiveStream(decoder=lambda bits: {}, checker=lambda graph: None)
        before = stream.snapshot()
        def fail(graph):
            raise MemoryError('resource failure is not an invalid proof')
        stream.checker = fail
        with self.assertRaises(MemoryError):
            stream.step()
        self.assertEqual(stream.snapshot(), before)

    def test_exact_cover_exhausts_all_contacts_instead_of_greedy_choice(self):
        library = ExactLibrary.__new__(ExactLibrary)
        library.checker = SimpleNamespace(cells=[None])
        library.statistics = dict(cover_queries=0)
        intervals = [((0, 0), (8, 3)), ((0, 0), (4, 4)),
                     ((4, 4), (7, 7)), ((7, 7), (10, 10))]
        library.usable = lambda cid, alive: [(a, b, dict(index=i)) for i, (a, b) in enumerate(intervals)
                                           if i in alive]
        def compare_vectors(domain, a, b, strict=False):
            return all(x > y if strict else x >= y for x, y in zip(a, b))
        with patch('complete_chart_library.compare', side_effect=compare_vectors):
            self.assertEqual([e['index'] for e in library.cover(0, (0, 0), (10, 10), set(range(4)))], [1, 2, 3])
            self.assertIsNone(library.cover(0, (0, 0), (10, 10), {0, 1, 3}))
            self.assertIsNone(library.cover(0, (0, 0), (10, 10), {0, 2, 3}))

    def test_real_bank_keeps_rules_and_guards_and_replays_negative_fixed_point(self):
        data, index, _ = split_rule()
        second = copy.deepcopy(data)
        second['nodes'][index]['children'] = second['nodes'][index]['pieces'][0]['children']
        del second['nodes'][index]['pieces']
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in complete finite search')):
            bank = build_bank([data, second])
            library = ExactLibrary(bank)
            alive = set(range(len(library.checker.nodes)))
            # Exact semantic merging must keep both uniform and guarded options.
            self.assertTrue(bank['layouts'])
            for graph in (data, second):
                source = PiecewiseVerifier(graph)
                for n in graph['nodes']:
                    if not n.get('children') and not n.get('pieces'):
                        continue
                    domain = source.cells[n['cell']]
                    candidates = [i for i, row in enumerate(library.checker.nodes)
                                  if library.checker.cells[row['cell']] == domain
                                  and row['lower'] == n['lower'] and row['upper'] == n['upper']]
                    self.assertTrue(candidates)
                    self.assertIsNotNone(library.query(candidates[0], alive))
            solver = FiniteClosure(len(alive), library.query)
            while solver.step():
                pass
            self.assertFalse(library.outcome(solver)['closed_in_this_menu'])
            audit = library.verify_fixed_point(solver)
            self.assertEqual(audit['failed'], 0)
            with self.assertRaisesRegex(ValueError, 'no completed closed'):
                library.certificate(solver)

    def test_deduplication_does_not_assume_hashes_are_injective(self):
        data, _, _ = split_rule()
        expected = build_bank([data])['offers']
        with patch('complete_chart_library.digest', return_value='forced collision'):
            actual = build_bank([data])['offers']
        self.assertEqual(actual, expected)


if __name__ == '__main__':
    unittest.main()
