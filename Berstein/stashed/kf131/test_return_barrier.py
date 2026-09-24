import copy
import json
from pathlib import Path
import unittest

from audit_return_barrier import audit


class ReturnBarrierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((Path(__file__).parent/'periodic_outer_all_five_coalesced_20260924.json').read_text())

    def test_only_central_root_returns_survive_in_saved_atlas(self):
        report = audit(self.data)
        self.assertTrue(report['closure_impossible_in_this_atlas'])
        self.assertEqual([r['edge']['suffixes'] for r in report['root_only_actions']],
                         [['2','2'],['22','22']])

    def test_does_not_claim_barrier_when_nonroot_can_cycle(self):
        data = copy.deepcopy(self.data)
        data['nodes'] = [copy.deepcopy(data['nodes'][0]) for _ in range(2)]
        for j,n in enumerate(data['nodes']):
            n.update(id=j,covered=False,children=[])
        report = audit(data,length=2)
        self.assertFalse(report['nonroot_potential_strictly_decreases'])
        self.assertFalse(report['closure_impossible_in_this_atlas'])


if __name__ == '__main__':
    unittest.main()
