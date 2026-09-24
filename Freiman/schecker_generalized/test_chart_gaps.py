import copy
from fractions import Fraction as F
import unittest
from unittest.mock import patch

from audit_chart_gaps import backward_trace, point_checker, probe, replay
from chart_geometry import Domain
from explore import Q
from type_graph_geometry import Cell, encode, full_labels, parameters
from verify_piecewise_charts import FORMAT, PiecewiseVerifier


def graph(domain):
    lower, upper = full_labels(domain.parity)
    return dict(format=FORMAT, cells=[domain.record()], roots={},
                nodes=[dict(cell=0, lower=lower, upper=upper, children=[])])


class ChartGapTests(unittest.TestCase):
    def test_backward_trace_respects_guards_and_exchange(self):
        base = Cell(('', ''), 1, True, (Q(F(2, 5)), Q(F(3, 5))),
                    (Q(F(1, 2)),)*2, (Q(F(1, 1000)),)*2)
        parent = Domain(base)
        child = parent.extend('2', '2', True).exchange()
        data = graph(parent)
        data['roots'] = dict(zero=0, positive=0)
        data['cells'].append(child.record())
        data['nodes'].append(dict(cell=1, lower=full_labels(1)[0],
                                  upper=full_labels(1)[1], children=[]))
        edge = dict(suffixes=['2', '2'], high=True,
                    destinations=[dict(node=1, swap=True)])
        data['nodes'][0]['children'] = [edge]
        checker = PiecewiseVerifier(data)
        row = probe(checker, 1, (1, 2))
        self.assertIsNotNone(row)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in trace')):
            trace = backward_trace(checker, row)
            self.assertEqual(trace['status'], 'inconclusive')
            self.assertEqual(trace['parents'][0]['status'], 'possible_from_root_box')
            narrow = Cell(base.states, base.parity, base.high,
                          (Q(F(2, 5)), Q(F(9, 20))), base.s, base.ratio)
            data['cells'].append(Domain(narrow).record())
            data['nodes'][0]['children'] = []
            data['nodes'][0]['pieces'] = [dict(cell=2, children=[edge])]
            excluded = backward_trace(PiecewiseVerifier(data), row)
            self.assertEqual(excluded['status'], 'excluded')

    def test_correlated_point_image_matches_actual_word_prefixes(self):
        base = parameters('32113', '4322')
        domain = Domain(base, ('12', '3'), False)
        checker = PiecewiseVerifier(graph(domain))
        actual = point_checker(checker, 0, (base.r[0], base.s[0], base.ratio[0])).cells[0]
        self.assertEqual(actual, parameters('3211312', '43223', False))

    def test_gap_exact_replay_rejects_tampered_point_and_interval(self):
        base = Cell(('', ''), 1, True, (Q(F(1, 2)),)*2,
                    (Q(F(1, 2)),)*2, (Q(F(1, 1000)),)*2)
        checker = PiecewiseVerifier(graph(Domain(base)))
        row = probe(checker, 0, (1,))
        self.assertIsNotNone(row)
        with patch.object(Q, 'decimal', side_effect=AssertionError('float in replay')):
            self.assertGreater(replay(checker, row)['comparisons'], 0)
            forged = copy.deepcopy(row)
            forged['base_parameters'][0] = encode(Q(2))
            with self.assertRaisesRegex(ValueError, 'outside base chart'):
                replay(checker, forged)
            forged = copy.deepcopy(row)
            forged['witness']['gap'].reverse()
            with self.assertRaises(ValueError):
                replay(checker, forged)


if __name__ == '__main__':
    unittest.main()
