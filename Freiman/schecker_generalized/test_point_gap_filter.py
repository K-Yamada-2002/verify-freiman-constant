import unittest
import copy
import json
from functools import lru_cache
from types import SimpleNamespace
from fractions import Fraction
from unittest.mock import patch

from chart_geometry import Domain
from cyclic_frontier_gaps import value, verify_witness
from explore import Q
from type_graph_geometry import Cell, encode, parameters, endpoint, full_labels
from audit_chart_gaps import probe
from test_chart_gaps import graph
from verify_piecewise_charts import PiecewiseVerifier
from verify_cyclic_types import Verifier

from repair_root_point_gap import bank_entry, contains_point, equivalent_gaps, install_bank, install_filter, known_gap_hits


class PointGapFilterTests(unittest.TestCase):
    def test_only_matching_geometry_is_split_and_old_rejections_stay(self):
        cell = SimpleNamespace(r=(Q(),)*2, s=(Q(),)*2, ratio=(Q(1),)*2,
                               anchors=lambda: (Q(), Q()), parity=1)
        search = SimpleNamespace(
            cells=[SimpleNamespace(outer=cell), SimpleNamespace(outer='other')],
            outer_memberships=lambda cid: (0, 0, 0, -1, 1),
            points=lambda cid: [(None, None, (Q(x), Q())) for x in
                                (0, Fraction(3, 2), 3, 4, 5)],
            moves=lru_cache(None)(lambda: None),
            native_geometry=lru_cache(None)(lambda: None))
        matched = install_filter(search, cell, Q(1), Q(2))
        a = search.outer_memberships(0)
        self.assertEqual(a[1], -1)
        self.assertEqual(a[3], -1)
        self.assertNotEqual(a[0], a[2])
        self.assertNotEqual(a[2], a[4])
        self.assertEqual(search.outer_memberships(1), (0, 0, 0, -1, 1))
        self.assertEqual(matched, {0})

    def test_empty_gap_is_rejected(self):
        with self.assertRaises(ValueError):
            install_filter(None, None, 1, 1)

    def test_transformed_chart_uses_witness_normalization_without_floats(self):
        domain = Domain(parameters('32113', '4322')).extend('3', '', True)
        cell = domain.outer
        xy = endpoint(cell.states, full_labels(cell.parity)[0])
        middle = value(cell, (cell.r[0], cell.s[0], cell.ratio[0]), xy)
        search = SimpleNamespace(cells=[domain],
            outer_memberships=lambda cid: (0,), points=lambda cid: [(None, None, xy)],
            value=lambda *args: self.fail('base-chart normalization must not be used'),
            moves=lru_cache(None)(lambda: None),
            native_geometry=lru_cache(None)(lambda: None))
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in point filter')):
            install_filter(search, cell, middle-Q(Fraction(1, 1000)), middle+Q(Fraction(1, 1000)))
            self.assertEqual(search.outer_memberships(0), (-1,))

    def test_point_membership_is_checked_in_correlated_chart(self):
        base = Cell(('', ''), 1, True,
                    (Q(Fraction(2, 5)), Q(Fraction(3, 5))),
                    (Q(Fraction(1, 2)),)*2, (Q(Fraction(1, 1000)),)*2)
        def at(r, high):
            return Domain(Cell(base.states, base.parity, base.high,
                               (Q(r),)*2, base.s, base.ratio)).extend('2', '2', high).outer
        for high in (False, True):
            domain = Domain(base).extend('2', '2', high)
            self.assertTrue(contains_point(domain, at(Fraction(1, 2), high)))
            self.assertFalse(contains_point(domain, at(Fraction(7, 10), high)))

    def test_serialized_bank_replays_and_rejects_forgery(self):
        base = Cell(('', ''), 1, True, (Q(Fraction(1, 2)),)*2,
                    (Q(Fraction(1, 2)),)*2, (Q(Fraction(1, 1000)),)*2)
        checker = PiecewiseVerifier(graph(Domain(base)))
        row = probe(checker, 0, (1,))
        bank = json.loads(json.dumps([bank_entry(checker, row)]))
        with patch('repair_root_point_gap.install_filter', return_value=set()) as apply:
            self.assertEqual(install_bank(None, bank), [set()]*4)
            self.assertEqual(apply.call_count, 4)
            forged = copy.deepcopy(bank)
            forged[0]['witness']['gap'].reverse()
            with self.assertRaises(ValueError):
                install_bank(None, forged)

    def test_gap_normalization_is_invariant_under_anchor_change_and_exchange(self):
        for u in ('32113', '3211'):
            cell = parameters(u, '4322')
            xy = endpoint(cell.states, full_labels(cell.parity)[0])
            center = value(cell, (cell.r[0], cell.s[0], cell.ratio[0]), xy)
            delta = Q(Fraction(1, 10000))
            variants = list(equivalent_gaps(cell, center-delta, center+delta))
            self.assertEqual(len(variants), 4)
            for target, low, high, swap in variants:
                point = xy[::-1] if swap else xy
                transformed = value(target, (target.r[0], target.s[0], target.ratio[0]), point)
                self.assertEqual(transformed, (low+high)/2)
                self.assertLess(low, high)

    def test_bank_refutes_same_interval_after_anchor_change(self):
        base = Cell(('', ''), 1, True, (Q(Fraction(1, 2)),)*2,
                    (Q(Fraction(1, 2)),)*2, (Q(Fraction(1, 1000)),)*2)
        checker = PiecewiseVerifier(graph(Domain(base)))
        row = probe(checker, 0, (1,))
        bank = [bank_entry(checker, row)]
        changed = PiecewiseVerifier(graph(Domain(base, ('', ''), False)))
        hits = known_gap_hits(changed, [0], bank)
        self.assertEqual([hit['node'] for hit in hits], [0])
        self.assertFalse(hits[0]['cell']['high'])

    def test_transformed_gap_witnesses_replay_independently(self):
        from type_graph_geometry import decode
        for parity in (-1, 1):
            base = Cell(('', ''), parity, True, (Q(Fraction(1, 2)),)*2,
                        (Q(Fraction(1, 2)),)*2, (Q(Fraction(1, 1000)),)*2)
            checker = PiecewiseVerifier(graph(Domain(base)))
            row = probe(checker, 0, (1,))
            low, high = map(decode, row['witness']['gap'])
            for cell, a, b, _ in equivalent_gaps(base, low, high):
                lower, upper = full_labels(cell.parity)
                target = Verifier(dict(format='freiman-cyclic-types-v1',
                    cells=[cell.record()], roots={}, nodes=[dict(
                        cell=0, lower=lower, upper=upper, children=[])]))
                witness = copy.deepcopy(row['witness'])
                witness.update(parameters=list(map(encode, (cell.r[0], cell.s[0], cell.ratio[0]))),
                               gap=[encode(a), encode(b)])
                self.assertGreater(verify_witness(target, witness)['comparisons'], 0)


if __name__ == '__main__':
    unittest.main()
