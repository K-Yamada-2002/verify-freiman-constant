import json
from pathlib import Path
import unittest

from exact import F
from close_scalar_library import common_fragments,close,RatioIndex


class LibraryClosureTests(unittest.TestCase):
    def test_ratio_index_preserves_nested_boxes_and_boundary_contacts(self):
        boxes=[(0,(F(0),F(10))),(1,(F(2),F(3))),(2,(F(3),F(4))),(3,(F(7),F(8)))]
        index=RatioIndex(boxes)
        for a,b in [(3,3),(4,7),(11,12),(-1,0),(0,10),(F(5,2),F(7,2))]:
            self.assertEqual(index.intersecting((a,b)),
                             [j for j,(c,d) in boxes if max(a,c)<=min(b,d)])

    def test_scalar_and_ratio_projections_do_not_suffice(self):
        rectangles = [((F(0),F(1,2)),(0,4)),((F(1,2),F(1)),(6,10))]
        self.assertEqual(common_fragments((F(0),F(1)),rectangles),[])

    def test_all_ratio_strips_must_share_the_scalar_interval(self):
        rectangles = [((F(0),F(1,2)),(0,6)),((F(1,2),F(1)),(4,10))]
        self.assertEqual(common_fragments((F(0),F(1)),rectangles),[(4,6)])

    def test_redundant_rectangle_can_be_removed_without_losing_cover(self):
        essential = [((F(0),F(1)),(0,10))]
        redundant = ((F(0),F(1,2)),(0,3))
        self.assertEqual(common_fragments((F(0),F(1)),essential+[redundant]),
                         common_fragments((F(0),F(1)),essential))

    def test_central_periodic_return_does_not_close(self):
        data = json.loads((Path(__file__).parent/'periodic_return_seed_20260924.json').read_text())
        graph,report = close(data,length=2)
        self.assertFalse(report['closed'])
        self.assertEqual(report['supported_nodes'],[])
        self.assertFalse(graph['nodes'][0]['covered'])

    def test_verified_local_rules_survive_the_first_deletion_round(self):
        data = json.loads((Path(__file__).parent/'periodic_outer_atom_current_20260924.json').read_text())
        _,report = close(data,length=2)
        covered = {j for j,n in enumerate(data['nodes']) if n['covered']}
        self.assertFalse(covered.intersection(report['rounds'][0]['removed']))
        self.assertEqual(report['supported_nodes'],[])

    def test_long_shape_return_blocks_do_not_turn_a_contraction_into_a_cover(self):
        data = json.loads((Path(__file__).parent/'periodic_return_seed_20260924.json').read_text())
        _,report = close(data,length=2,return_blocks=True)
        self.assertGreater(report['longest_retained_move'],2)
        self.assertFalse(report['closed'])
        self.assertEqual(report['supported_nodes'],[])


if __name__ == '__main__':
    unittest.main()
