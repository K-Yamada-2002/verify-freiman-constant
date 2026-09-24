import copy
import json
from pathlib import Path
import unittest

from split_scalar_obligations import split
from verify_scalar_graph import ScalarVerifier


class SplitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((Path(__file__).parent/'periodic_outer_atom_current_20260924.json').read_text())

    def test_union_and_physical_seed_are_preserved(self):
        result,report = split(self.data)
        self.assertEqual(ScalarVerifier(result).seed(),ScalarVerifier(self.data).seed())
        for j,ids in report['partitions'].items():
            intervals = [result['nodes'][k]['interval'] for k in ids]
            self.assertEqual(intervals[0][0],self.data['nodes'][j]['interval'][0])
            self.assertEqual(intervals[-1][1],self.data['nodes'][j]['interval'][1])
            self.assertTrue(all(a[1] == b[0] for a,b in zip(intervals,intervals[1:])))
            self.assertTrue(all(not result['nodes'][k]['covered'] for k in ids))
        self.assertEqual(len(report['local_checks']),10)
        with self.assertRaisesRegex(ValueError,'open obligation'):
            ScalarVerifier(result).closed()

    def test_missing_middle_piece_is_not_accepted_as_parent_cover(self):
        result,report = split(self.data)
        missing = report['partitions'][9][1]
        broken = copy.deepcopy(result)
        affected = []
        for n in broken['nodes']:
            for edge in n['children']:
                for case in edge['cases']:
                    if missing in case['destinations']:
                        case['destinations'].remove(missing)
                        affected.append(n['id'])
        self.assertTrue(affected)
        for j in affected:
            with self.assertRaises(ValueError):
                ScalarVerifier(broken).local(j)

    def test_cannot_split_an_already_covered_root(self):
        with self.assertRaisesRegex(ValueError,'open non-root'):
            split(self.data,targets=[0])

    def test_nonuniform_partition_preserves_a_narrow_middle_bridge(self):
        a,b = self.data['nodes'][9]['interval']
        middle = (a+b)//2
        result,report = split(self.data,targets=[9],cut_points={9:[middle-1,middle+1]})
        ids = report['partitions'][9]
        self.assertEqual([result['nodes'][j]['interval'] for j in ids],
                         [[a,middle-1],[middle-1,middle+1],[middle+1,b]])
        with self.assertRaisesRegex(ValueError,'invalid interior cut'):
            split(self.data,targets=[9],cut_points={9:[middle+1,middle-1]})


if __name__ == '__main__':
    unittest.main()
