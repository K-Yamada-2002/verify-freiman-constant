from collections import deque
import random
import unittest

from chart_strategy_ranks import ranks


class RankTests(unittest.TestCase):
    def test_random_graphs_against_independent_shortest_open_paths(self):
        rng=random.Random(462)
        for _ in range(100):
            children=[set(rng.sample(range(12),rng.randrange(4))) for i in range(12)]
            nodes=[dict(cell=0,children=[dict(destinations=[dict(node=j) for j in sorted(ds)])]
                        if ds else []) for ds in children]
            expected=[]
            for root in range(12):
                queue=deque([(root,0)]);seen=set();found=None
                while queue:
                    i,d=queue.popleft()
                    if i in seen:continue
                    seen.add(i)
                    if not children[i]:found=d;break
                    queue.extend((j,d+1) for j in children[i])
                expected.append(found)
            self.assertEqual(ranks(dict(nodes=nodes)),expected)

    def test_one_open_exit_prevents_a_cycle_from_being_closed(self):
        data=dict(nodes=[dict(cell=0,children=[dict(destinations=[dict(node=1)])]),
                         dict(cell=0,children=[dict(destinations=[dict(node=0),dict(node=2)])]),
                         dict(cell=0,children=[])])
        self.assertEqual(ranks(data),[2,1,0])


if __name__=='__main__':unittest.main()
