import unittest
from unittest.mock import patch

from chart_geometry import relative_box
from contract_cyclic_domains import domains
from explore import Q
from finite_type_game import Game
from search_known_chart_returns import KnownReturnSearch
from type_graph_geometry import full_labels


class KnownReturnTests(unittest.TestCase):
    def test_nonroot_saved_chart_and_exchanged_chart_are_return_options(self):
        search=KnownReturnSearch([],bins=1,outer_depth=0,partition_depth=0,
                                 shape_menu=[full_labels(1),full_labels(-1)])
        search.game=Game(search.roots())
        child=search.cells[0].extend('2','2',True)
        target=search.register(child)
        exchanged=search.register(child.exchange())
        search.initialize_returns([target,exchanged])
        routes=search.child_routes(0,'2','2',True)
        first=next(routes)[1]
        self.assertEqual(first,[(target,False)])
        options=[first,next(routes)[1]]
        self.assertIn([(exchanged,True)],options)
        for route in options:
            i,swap=route[0]
            actual=child.exchange() if swap else child
            with patch.object(Q,'decimal',side_effect=AssertionError('float in containment replay')):
                image=relative_box(actual,search.cells[i])
                self.assertTrue(all(a<=lo<=hi<=b for (a,b),(lo,hi) in
                                    zip(domains(search.cells[i].base),domains(image))))


if __name__=='__main__':
    unittest.main()
