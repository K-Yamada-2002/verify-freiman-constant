import copy
import json
from pathlib import Path
import unittest
from chart_geometry import Domain
from finite_type_game import Game
from search_interval_fragments import FragmentSearch, compile_fragments, intersect_domains
from search_piecewise_charts import PiecewiseSearch
from type_graph_geometry import Cell, endpoint
from verify_piecewise_charts import PiecewiseVerifier


class FragmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        source=json.loads((Path(__file__).parent/'zero_round2_repaired_expansion.json').read_text())
        root=source['nodes'][0]
        indices=[0,1]+[d['node'] for r in source['nodes'][:2] for e in r['children'] for d in e['destinations']]
        labels={tuple(n[k]) for i in indices for n in [source['nodes'][i]] for k in ('lower','upper')}
        labels.update(tuple(e[k]) for r in source['nodes'][:2] for e in r['children'] for k in ('lower','upper'))
        cls.search=FragmentSearch(labels,bins=1,outer_depth=0,partition_depth=0,shape_menu=[(source['nodes'][i]['lower'],source['nodes'][i]['upper']) for i in indices])
        keys={}
        for i in indices:
            n=source['nodes'][i];cid=cls.search.register(Domain.read(source['cells'][n['cell']]))
            lookup={p[2]:j for j,p in enumerate(cls.search.points(cid))}
            keys[i]=(cid,*(lookup[endpoint(cls.search.cells[cid].states,n[k])] for k in ('lower','upper')))
        cls.key=keys[0];cls.positive_key=keys[1]
        cls.plan=copy.deepcopy(root['children']);cls.positive_plan=copy.deepcopy(source['nodes'][1]['children'])
        for e in cls.plan+cls.positive_plan:
            e['destinations']=[dict(key=keys[d['node']],swap=d['swap']) for d in e['destinations']]

    def test_partition_compiles_and_retains_real_children(self):
        plan,deps=compile_fragments(self.search,self.key,[(self.plan[:1],[]),(self.plan[1:],[])])
        self.assertEqual(plan,self.plan)
        self.assertEqual(set(deps),{d['key'] for e in self.plan for d in e['destinations']})
        self.assertTrue(all(any(e['suffixes']) for e in plan))
        # Local implication remains conditional: no terminal filling axiom.
        probe=Game([self.key])
        for child in deps:probe.add(child)
        probe.entries[0].update(status='local',plan=plan,children=[probe.ids[k] for k in deps])
        checker=PiecewiseVerifier(self.search.certificate(probe))
        for i in range(1,len(checker.nodes)):
            with self.assertRaises(ValueError):checker.local(i)

    def test_missing_middle_fragment_rejected(self):
        with self.assertRaises(ValueError):
            compile_fragments(self.search,self.key,[(self.plan[:1],[]),(self.plan[2:],[])])

    def test_missing_last_fragment_rejected(self):
        with self.assertRaises(ValueError):compile_fragments(self.search,self.key,[(self.plan[:2],[])])

    def test_parameter_guard_hole_rejected(self):
        cid=self.key[0];domain=self.search.cells[cid]
        # Use the positive-index root, whose base r interval has width.
        d=self.search.cells[1];a,b=d.base.r;mid=(a+b)/2
        left=Domain(Cell(d.base.states,d.base.parity,d.base.high,(a,mid),d.base.s,d.base.ratio),d.words,d.high)
        right=Domain(Cell(d.base.states,d.base.parity,d.base.high,((mid+b)/2,b),d.base.s,d.base.ratio),d.words,d.high)
        self.assertIsNone(intersect_domains(left,right))
        empty=dict(pieces=[])
        with self.assertRaises(ValueError):compile_fragments(self.search,self.key,[(empty,[])])

    def test_guard_common_refinement_and_missing_half(self):
        cid=self.positive_key[0];d=self.search.cells[cid]
        def split(axis):
            boxes=[d.base.r,d.base.s,d.base.ratio];a,b=boxes[axis];mid=(a+b)/2;ids=[]
            for bound in ((a,mid),(mid,b)):
                part=list(boxes);part[axis]=bound
                ids.append(self.search.register(Domain(Cell(d.base.states,d.base.parity,d.base.high,*part),d.words,d.high)))
            return ids
        left=split(0);right=split(1)
        a=dict(pieces=[dict(cell=i,children=self.positive_plan[:1]) for i in left])
        b=dict(pieces=[dict(cell=i,children=self.positive_plan[1:]) for i in right])
        plan,_=compile_fragments(self.search,self.positive_key,[(a,[]),(b,[])])
        self.assertEqual(len(plan['pieces']),4)
        a['pieces'].pop()
        with self.assertRaises(ValueError):compile_fragments(self.search,self.positive_key,[(a,[]),(b,[])])

    def test_new_target_endpoints_are_serializable(self):
        from learn_small_type_menu import template_labels
        cid,lo,hi=self.key;points=self.search.points(cid)
        mid=next(i for i in range(len(points)) if i not in (lo,hi))
        key=cid,lo,mid
        self.search.ensure_target_shape(key)
        template_labels(self.search.cells[cid].states,points[lo][2],points[mid][2],self.search.shape_menu)

    def test_wrong_chart_intersection_rejected(self):
        with self.assertRaises(ValueError):
            intersect_domains(self.search.cells[0],self.search.cells[0].extend('2','',True))

if __name__=='__main__':unittest.main()
