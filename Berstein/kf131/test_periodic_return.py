import contextlib
import copy
import io
import json
from pathlib import Path
import unittest

from add_gap_repair_moves import add_moves
from verify_scalar_graph import ScalarVerifier
from periodic_cycle_diagnostic import diagnose


class PeriodicReturnTests(unittest.TestCase):
    def test_exact_ratio_cycle_still_cannot_cover_scalar_intervals(self):
        source = Path(__file__).with_name('periodic_return_continued_20260924')/'current.json'
        data = json.loads(source.read_text())
        result = diagnose(data)
        self.assertTrue(result['parameter_cycle_exact'])
        self.assertTrue(result['positive_symmetric_two_edge_cycle_impossible'])
        # The assertion applies to a positive-width symmetric two-edge cycle.
        # A non-symmetric interval must not accidentally inherit that conclusion.
        data['nodes'][1]['interval'][0] += 1
        with self.assertRaisesRegex(ValueError, 'symmetric intervals'):
            diagnose(data)

    def test_exact_ratio_return_needs_no_touching_neighbor_boxes(self):
        data = json.loads(Path(__file__).with_name('periodic_return_seed_20260924.json').read_text())
        incoming = dict(settings=data['settings'],nodes={'0':copy.deepcopy(data['nodes'][0])},parents={'0':[]},rules=[])
        with contextlib.redirect_stdout(io.StringIO()):
            add_moves(incoming,[0],2,memory=8,refinement=6)
        edge = next(r['children'][0] for r in incoming['rules'] if r['children'][0]['suffixes']==['2','2'])
        self.assertEqual(len(edge['cases']),1)
        self.assertEqual(len(edge['cases'][0]['destinations']),1)
        child = incoming['nodes'][str(edge['cases'][0]['destinations'][0])]
        self.assertEqual(child['ratio_bin'],data['nodes'][0]['ratio_bin'])
        self.assertEqual(child['ratio_refinement'],data['nodes'][0]['ratio_refinement'])
        edge['cases'][0].update(interval=list(data['nodes'][0]['interval']),destinations=[0])
        data['nodes'][0].update(covered=True,children=[edge])
        v = ScalarVerifier(data)
        (a,b),dependencies = v.scalar_child(0,edge)
        lo,hi = v.interval(data['nodes'][0]['interval'])
        self.assertTrue(lo < a < 0 < b < hi)
        self.assertEqual(dependencies,[0])
        # A central self-return does not cover the two outer pieces.
        with self.assertRaises(ValueError):
            v.closed()


if __name__ == '__main__':
    unittest.main()
