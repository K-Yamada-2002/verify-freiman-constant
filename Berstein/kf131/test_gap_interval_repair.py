import copy
import json
from pathlib import Path
import random
import unittest

from exact import F
from anchored_geometry import B
from repair_gap_intervals import rounded,subtract,gap_envelope
from verify_scalar_graph import ScalarVerifier
from graft_gap_repairs import graft,geometry


class GapIntervalRepairTest(unittest.TestCase):
    def test_empty_gap_envelopes_do_not_split_an_interval(self):
        self.assertEqual(subtract((0,10),[(7,3),(5,5)]),[(0,10)])

    def test_exact_rounding(self):
        for x in (B(-1,1),B(1,-1),B(F(-1,4)),B(F(3,2))):
            for grid in (1,10,1024,1024000000):
                a,b = rounded(x,grid,False),rounded(x,grid,True)
                self.assertTrue(F(a,grid) <= x <= F(b,grid))
                self.assertTrue(x < F(a+1,grid) and F(b-1,grid) < x)

    def test_subtraction_against_points(self):
        rng = random.Random(87)
        for _ in range(300):
            cuts = [sorted(rng.sample(range(-10,11),2)) for _ in range(6)]
            parts = subtract((-8,8),cuts)
            for k in range(-17,18):
                t = F(k,2)
                # Cut boundaries are allowed to remain in adjacent closed parts.
                if any(t == a or t == b for a,b in cuts):
                    continue
                expected = -8 <= t <= 8 and not any(a < t < b for a,b in cuts)
                self.assertEqual(any(a <= t <= b for a,b in parts),expected)

    def test_saved_parent_covers(self):
        path = Path(__file__).with_name('gap_repaired_20260924.json')
        data = json.loads(path.read_text())
        checker = ScalarVerifier(data)
        self.assertEqual(len(data['roots']),14)
        for j in data['roots']:
            self.assertTrue(checker.local(j)['dependencies'])
        self.assertEqual(sum(n['covered'] for n in data['nodes']),len(data['roots']))
        self.assertTrue(data['open_nodes'] > 0)
        with self.assertRaisesRegex(ValueError,'open obligation'):
            checker.closed()

    def test_missing_bridge_rejected(self):
        data = json.loads(Path(__file__).with_name('gap_repaired_20260924.json').read_text())
        j = next(j for j in data['roots'] if data['nodes'][j]['source_node'] == 390931)
        self.assertEqual(len(data['nodes'][j]['children']),2)
        data['nodes'][j]['children'].pop()
        with self.assertRaisesRegex(ValueError,'upper end is not covered'):
            ScalarVerifier(data).local(j)

    def test_missing_parameter_strip_rejected(self):
        data = json.loads(Path(__file__).with_name('gap_repaired_20260924.json').read_text())
        j = data['roots'][0]
        data['nodes'][j]['children'][0]['cases'][0]['destinations'] = []
        with self.assertRaisesRegex(ValueError,'empty destination'):
            ScalarVerifier(data).local(j)

    def test_gap_envelopes_enclose_known_bands(self):
        certs = json.loads(Path(__file__).with_name('scalar_obstructions_20260924.json').read_text())['obstructions']
        grid = 1024000000
        for cert in certs:
            if 'physical_scalar_gap' not in cert:
                continue
            a,b = gap_envelope(cert,grid)
            lo,hi = map(F,cert['physical_scalar_gap'])
            self.assertTrue(F(a,grid) < lo < hi < F(b,grid))

    def test_graft_preserves_roots_and_obligations(self):
        folder = Path(__file__).parent
        base = json.loads((folder/'gap_repaired_sieved_20260924.json').read_text())
        patch = json.loads((folder/'gap_split_children_sieved_20260924.json').read_text())
        result,report = graft(base,patch)
        def roots(data):
            return {(geometry(data['nodes'][j]),tuple(data['nodes'][j]['interval'])) for j in data['roots']}
        self.assertEqual(roots(base),roots(result))
        self.assertGreater(report['newly_covered_reachable'],0)
        checker = ScalarVerifier(result)
        for n in result['nodes']:
            if n['covered']:
                self.assertTrue(checker.local(n['id'])['dependencies'])
        with self.assertRaisesRegex(ValueError,'open obligation'):
            checker.closed()

    def test_new_roots_are_only_added_explicitly(self):
        folder = Path(__file__).parent
        data = json.loads((folder/'gap_repaired_sieved_20260924.json').read_text())
        patch = copy.deepcopy(data)
        base = copy.deepcopy(data)
        base['roots'] = data['roots'][:1]
        ordinary,_ = graft(base,patch)
        combined,_ = graft(base,patch,True)
        self.assertEqual(len(ordinary['roots']),1)
        self.assertEqual(len(combined['roots']),len(data['roots']))


if __name__ == '__main__':
    unittest.main()
