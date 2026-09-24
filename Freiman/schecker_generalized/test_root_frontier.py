from collections import deque
from types import SimpleNamespace
import unittest

from finite_type_game import Game
from search_root_frontier import prioritize


class RootFrontierTests(unittest.TestCase):
    def test_shortest_open_branch_precedes_popular_deeper_branch(self):
        game=Game([0])
        for i in range(1,5):game.add(i)
        game.entries[0].update(status='local',children=[1,2])
        game.entries[1].update(status='local',children=[0,3])
        game.entries[3].update(status='local',children=[4])
        game.entries[4]['parents']=set(range(10))
        lane=SimpleNamespace(game=game,todo=deque([4,2]))
        depth=prioritize(lane)
        self.assertEqual(list(lane.todo),[2,4])
        self.assertEqual((depth[2],depth[4]),(1,3))

    def test_focus_keeps_other_root_but_does_not_prioritize_its_frontier(self):
        game=Game([0,1])
        for i in (2,3):game.add(i)
        game.entries[0].update(status='local',children=[2])
        game.entries[1].update(status='local',children=[3])
        lane=SimpleNamespace(game=game,todo=deque([3,2]))
        depth=prioritize(lane,[0])
        self.assertEqual(list(lane.todo),[2,3])
        self.assertNotIn(3,depth)
        self.assertEqual(game.roots,[0,1])


if __name__=='__main__':unittest.main()
