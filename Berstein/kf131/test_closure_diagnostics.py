import random
import unittest

from closure_diagnostics import deletion_ranks


def data_for(n, rules):
    return dict(nodes=[{} for _ in range(n)],alternative_rules=[
        dict(parent=p,children=[dict(cases=[dict(destinations=children)])])
        for p,children in rules])


class DeletionRanksTest(unittest.TestCase):
    def test_cycles_require_all_children(self):
        self.assertEqual(deletion_ranks(data_for(3,[(0,[1]),(1,[0,2])])),[2,1,0])
        self.assertEqual(deletion_ranks(data_for(3,[(0,[1]),(1,[0,2]),(1,[0])])),[None,None,0])

    def test_against_synchronous_elimination(self):
        rng = random.Random(1249)
        for _ in range(1000):
            n = rng.randrange(1,9)
            rules = [(rng.randrange(n),rng.sample(range(n),rng.randrange(n+1)))
                     for _ in range(rng.randrange(20))]
            alive = set(range(n))
            expected = [None]*n
            for rank in range(n+1):
                new = {p for p,c in rules if p in alive and set(c) <= alive}
                for i in alive-new:
                    expected[i] = rank
                if new == alive:
                    break
                alive = new
            self.assertEqual(deletion_ranks(data_for(n,rules)),expected)


if __name__ == '__main__':
    unittest.main()
