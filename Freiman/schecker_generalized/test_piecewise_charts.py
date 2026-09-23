import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from chart_geometry import Domain
from explore import Q
from finite_type_game import Game
from search_piecewise_charts import PiecewiseSearch, fingerprint, restore
from test_frontier_repair import small_graph
from type_graph_geometry import Cell, endpoint, full_labels
from verify_piecewise_charts import FORMAT, PiecewiseVerifier
from piecewise_chart_example import verify as verify_example


def split_rule():
    data=small_graph();data['format']=FORMAT
    checker=PiecewiseVerifier(data)
    index=next(i for i,n in enumerate(data['nodes']) if n['children'] and any(
        a!=b for a,b in (checker.cells[n['cell']].base.r,checker.cells[n['cell']].base.s,
                        checker.cells[n['cell']].base.ratio)))
    n=data['nodes'][index];domain=checker.cells[n['cell']];base=domain.base
    bounds=[base.r,base.s,base.ratio];axis=next(i for i,b in enumerate(bounds) if b[0]!=b[1])
    lo,hi=bounds[axis];mid=(lo+hi)/2
    n['pieces']=[]
    for interval in ((lo,mid),(mid,hi)):
        bb=list(bounds);bb[axis]=interval
        d=Domain(Cell(base.states,base.parity,base.high,*bb),domain.words,domain.high)
        n['pieces'].append(dict(cell=len(data['cells']),children=copy.deepcopy(n['children'])))
        data['cells'].append(d.record())
    n['children']=[]
    return data,index,axis


class PiecewiseTests(unittest.TestCase):
    def test_real_piecewise_example_and_uniform_counterexamples_without_floats(self):
        record=json.loads(Path(__file__).with_name('piecewise_chart_example.json').read_text())
        with patch.object(Q,'decimal',side_effect=AssertionError('float in exact example')):
            result=verify_example(record)
        self.assertEqual(result['pieces'],2)
        self.assertTrue(result['unproved_dependencies'])

    def test_piecewise_rule_replays_exactly_and_remains_open(self):
        data,index,_=split_rule();checker=PiecewiseVerifier(data)
        with patch.object(Q,'decimal',side_effect=AssertionError('float in exact guard checker')):
            self.assertEqual(checker.local(index)['parameter_pieces'],2)
            audit=checker.audit()
        self.assertFalse(audit['failed_rules'])
        self.assertTrue(audit['open_nodes'])
        with self.assertRaisesRegex(ValueError,'unresolved'):
            checker.closed()

    def test_missing_parameter_piece_is_rejected(self):
        data,index,_=split_rule();data['nodes'][index]['pieces'].pop()
        with self.assertRaisesRegex(ValueError,'gap|uncovered'):
            PiecewiseVerifier(data).local(index)

    def test_empty_suffix_inside_a_piece_is_rejected(self):
        data,index,_=split_rule()
        data['nodes'][index]['pieces'][0]['children'][0]['suffixes']=['','']
        with self.assertRaisesRegex(ValueError,'empty'):
            PiecewiseVerifier(data).local(index)

    def test_omitting_a_piece_cover_is_rejected(self):
        data,index,_=split_rule();data['nodes'][index]['pieces'][0]['children']=[]
        with self.assertRaisesRegex(ValueError,'unresolved parameter piece'):
            PiecewiseVerifier(data).local(index)

    def test_split_changes_coordinates_without_changing_semantics(self):
        s=PiecewiseSearch([],bins=1,outer_depth=0,partition_depth=2,
                         shape_menu=[full_labels(1),full_labels(-1)])
        parts=s.split(1)
        self.assertEqual(len(parts),2)
        for cid in parts:
            p=s.points(cid)[0][0]
            self.assertEqual(s.native_cell(cid)[0],s.cells[cid].base.parity)
            self.assertEqual(s.value(cid,p),s.routing.value(s.base_ids[s.cells[cid].base],p))
            for leaf in s.split(cid):
                self.assertEqual(s.split(leaf),[])

    def test_failed_first_axis_does_not_hide_a_successful_second_axis(self):
        s=PiecewiseSearch([],bins=1,outer_depth=0,partition_depth=1,
                         shape_menu=[full_labels(1),full_labels(-1)])
        base=next(c for c in s.routing.cells if c.states==('1','1') and c.parity==1 and c.high)
        cid=s.register(Domain(base,('',''),True))
        lookup={p[2]:i for i,p in enumerate(s.points(cid))}
        key=(cid,*(lookup[endpoint(base.states,z)] for z in full_labels(1)))
        s.game=Game([key])
        def stub(k,rejected):
            cell=s.cells[k[0]].base
            # Discovery-only stub: a split in s works; a split in r does not.
            return ([],[]) if cell.r==base.r and cell.s!=base.s else None
        with patch.object(s,'_plan_once',side_effect=stub):
            leaves=s.leaf_plans(key)
        self.assertEqual(len(leaves),2)
        self.assertGreaterEqual(s.partition_statistics['axis_trials'],2)
        self.assertTrue(all(s.cells[k[0]].base.r==base.r for k,_ in leaves))

    def test_guarded_state_roundtrip_keeps_all_dependencies(self):
        s=PiecewiseSearch([],bins=1,outer_depth=0,partition_depth=2,
                         shape_menu=[full_labels(1),full_labels(-1)])
        g=Game(s.roots());s.game=g
        # This tests serialization, not a proof: no unverified rule is passed
        # through an engine migration or claimed as closed.
        cid=s.split(1)[0];key=(cid,g.keys[1][1],g.keys[1][2]);j=g.add(key)
        g.entries[0].update(status='local',plan=dict(pieces=[dict(cell=cid,children=[])]),children=[j])
        g.entries[j]['parents'].add(0)
        config=dict(bins=1,base='22/25',balance='0',outer_depth=0,partition_depth=2)
        state=json.loads(json.dumps(s.snapshot(g,config,fingerprint())))
        ss,gg,_=restore(state)
        self.assertEqual(json.loads(json.dumps(g.snapshot())),json.loads(json.dumps(gg.snapshot())))
        self.assertEqual(s.partition_levels,ss.partition_levels)
        self.assertEqual(json.loads(json.dumps(s.certificate(g))),json.loads(json.dumps(ss.certificate(gg))))


if __name__=='__main__':
    unittest.main()
