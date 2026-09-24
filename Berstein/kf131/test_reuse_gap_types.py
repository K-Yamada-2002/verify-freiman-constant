import copy
import json
from pathlib import Path
import unittest

from repair_gap_intervals import library_cover,library_fragments,choose_candidate
from verify_scalar_graph import ScalarVerifier
from closure_diagnostics import deletion_ranks


class ReuseGapTypesTest(unittest.TestCase):
    def test_shorter_return_is_kept_before_fresh_larger_offer(self):
        old = ((0,5),dict(cases=[dict(destinations=[0])]),False,0)
        fresh = ((0,10),dict(cases=[dict(destinations=[1])]),False,1)
        self.assertEqual(choose_candidate([old,fresh],{0}),fresh)
        self.assertEqual(choose_candidate([old,fresh],{0},True),old)
        current = 0
        selected = []
        while current < 10:
            choices = [c for c in [old,fresh] if c[0][0] <= current < c[0][1]]
            item = choose_candidate(choices,{0},True)
            selected.append(item[3]);current = item[0][1]
        self.assertEqual(selected,[0,1])

    def checker(self):
        source = json.loads(Path(__file__).with_name('gap_repair_current_20260924.json').read_text())
        row = copy.deepcopy(source['nodes'][0])
        row.update(interval=[0,10],ratio_refinement=[0,0],children=[],covered=False)
        nodes = [copy.deepcopy(row) for _ in range(4)]
        for j,n in enumerate(nodes):
            n['id'] = j
        return ScalarVerifier(dict(schema=source['schema'],settings=source['settings'],nodes=nodes))

    def test_two_intervals_reuse_one_whole_box(self):
        v = self.checker()
        v.nodes[1]['interval'] = [0,6]
        v.nodes[2]['interval'] = [5,10]
        self.assertEqual(library_cover(v,0,(0,10),[1,2]),[1,2])

    def test_scalar_hole_not_covered(self):
        v = self.checker()
        v.nodes[1]['interval'] = [0,4]
        v.nodes[2]['interval'] = [5,10]
        self.assertIsNone(library_cover(v,0,(0,10),[1,2]))

    def test_smaller_existing_domain_is_still_an_offer(self):
        v = self.checker()
        v.nodes[1]['interval'] = [2,7]
        self.assertIsNone(library_cover(v,0,(0,10),[1]))
        self.assertEqual(library_fragments(v,[0],(0,10),[[1]]),[(2,7)])

    def test_fragments_intersect_across_required_parameter_boxes(self):
        v = self.checker()
        v.nodes[1]['interval'] = [1,7]
        v.nodes[2]['interval'] = [4,9]
        self.assertEqual(library_fragments(v,[0,0],(0,10),[[1],[2]]),[(4,7)])

    def test_fragment_does_not_bridge_scalar_gap(self):
        v = self.checker()
        v.nodes[1]['interval'] = [0,4]
        v.nodes[2]['interval'] = [5,10]
        self.assertEqual(library_fragments(v,[0],(0,10),[[1,2]]),[(0,4),(5,10)])

    def test_parameter_intersection_is_insufficient(self):
        v = self.checker()
        v.nodes[1]['ratio_refinement'] = [1,0]
        self.assertIsNone(library_cover(v,0,(0,10),[1]))

    def test_coarser_parameter_box_can_be_reused(self):
        v = self.checker()
        v.nodes[0]['ratio_refinement'] = [2,1]
        self.assertEqual(library_cover(v,0,(0,10),[1]),[1])

    def test_wrong_parity_and_refuted_type_rejected(self):
        v = self.checker()
        v.nodes[1]['parity'] *= -1
        self.assertIsNone(library_cover(v,0,(0,10),[1]))
        self.assertIsNone(library_cover(v,0,(0,10),[2],lambda j:False))

    def test_return_is_not_closure_with_an_open_child(self):
        data = dict(nodes=[{},{}],alternative_rules=[dict(parent=0,children=[dict(cases=[dict(destinations=[0,1])])])])
        self.assertEqual(deletion_ranks(data),[1,0])


if __name__ == '__main__':
    unittest.main()
