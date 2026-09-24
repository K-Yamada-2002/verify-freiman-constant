import copy
import json
from pathlib import Path
import unittest
import random

from audit_whole_scalar_intervals import sampled_gaps,witnesses,outer_sum_gaps,adaptive_tails
from continue_gap_closure import refuted_roots
from exact import F
from scalar_obstructions import replay
from verify_scalar_graph import ScalarVerifier


class WholeIntervalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).parent
        cls.graph = json.loads((path/'gap_repair_current_20260924.json').read_text())
        cls.certs = json.loads((path/'closure_root_obstructions_20260924.json').read_text())['obstructions']

    def test_gap_between_old_sample_points(self):
        cert = self.certs[0]
        v = ScalarVerifier(self.graph)
        node = cert['type']
        a,b = v.interval(node['interval'])
        t = F(cert['target'])
        self.assertNotIn(t,(a,b,(a+b)/2,(3*a+b)/4,(a+3*b)/4))
        gaps = sampled_gaps(node,tuple(map(F,cert['parameters'])),(a,b),7)
        self.assertTrue(any(lo < float(t) < hi for lo,hi in gaps))
        self.assertGreater(replay(cert)['leaves'],0)

    def test_refuted_fixed_roots(self):
        self.assertEqual({r['root'] for r in refuted_roots(self.graph,self.certs)},
                         {c['graph_node'] for c in self.certs})

    def test_witness_outside_new_root_does_not_refute_it(self):
        graph = copy.deepcopy(self.graph)
        cert = self.certs[0]
        j = cert['graph_node']
        graph['roots'] = [j]
        graph['nodes'][j]['interval'] = [339000000,339100000]
        self.assertEqual(refuted_roots(graph,[cert]),[])

    def test_root_guard_replays_completeness(self):
        cert = copy.deepcopy(self.certs[0])
        cert['tree'][0]['children'].pop()
        with self.assertRaisesRegex(ValueError,'incomplete legal split'):
            refuted_roots(self.graph,[cert])

    def test_parameter_samples_inside_boxes(self):
        v = ScalarVerifier(self.graph)
        boxes = v.box(self.certs[0]['graph_node'])
        points = list(witnesses(boxes,True))
        self.assertEqual(len(points),9)
        for point in points:
            self.assertTrue(all(a < t < b for t,(a,b) in zip(point,boxes)))

    def test_grouped_sums_match_full_pairwise_union(self):
        rng = random.Random(427)
        for _ in range(100):
            families = []
            for side in range(2):
                ends = sorted(rng.sample(range(-500,501),40))
                families.append(list(zip(ends[::2],ends[1::2])))
            sums = sorted((a+c,b+d) for a,b in families[0] for c,d in families[1])
            low,high = sorted(rng.sample(range(-1000,1001),2))
            current = low
            expected = []
            for a,b in sums:
                a,b = max(low,a),min(high,b)
                if b < current or a > high:
                    continue
                if current < a:
                    expected.append((current,a))
                current = max(current,b)
            if current < high:
                expected.append((current,high))
            self.assertEqual(sorted(outer_sum_gaps(*families,(low,high))),sorted(expected))

    def test_adaptive_cover_resolves_slow_cylinders(self):
        alpha = 2**0.5-1
        for state in ('','1','13'):
            leaves = adaptive_tails(state,1e-4)
            self.assertTrue(all(0 < b-a <= 1e-4 for a,b in leaves))
            self.assertTrue(any(a <= alpha <= b for a,b in leaves))

    def test_large_union_compaction_keeps_gaps_and_can_finish_early(self):
        right = [(3*j,3*j+1) for j in range(10000)]
        gaps = outer_sum_gaps([(0,0),(1,1)],right,(0,30000))
        self.assertEqual(sorted(gaps),[(3*j+2,3*j+3) for j in range(10000)])
        self.assertEqual(outer_sum_gaps([(0,0),(1,2)],right,(0,30000)),[])


if __name__ == '__main__':
    unittest.main()
