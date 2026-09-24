import copy
import json
from pathlib import Path
import unittest
from exact import F
from scalar_obstructions import rational_in
from verify_scalar_graph import verifier_for
from audit_affine_bands import replay_band


class BandObstructionTests(unittest.TestCase):
    def certificate(self):
        data=json.loads((Path(__file__).parent/'affine_band_extended_runs_20260925/stage_00.json.last_nonempty.json').read_text())
        node=copy.deepcopy(data['nodes'][0])
        node.update(interval=[1000,1001],scalar_slope='1/8')
        settings=dict(data['settings'],grid=100)
        v=verifier_for(dict(schema='kf131-sloped-atlas-v1',settings=settings,nodes=[node]))
        params=list(map(rational_in,v.box(0)))
        t=F(2001,200); g=t+params[2]/8
        constant=copy.deepcopy(node); constant.pop('scalar_slope')
        constant['interval']=[g.numerator-1,g.numerator+1]
        cert=dict(type=constant,settings=dict(settings,grid=g.denominator),parameters=list(map(str,params)),target=str(g),tree=[dict(u='',v='',children=[])])
        return dict(band_type=node,settings=settings,band_target=str(t),constant_certificate=cert)

    def test_exact_exclusion_after_coordinate_translation(self):
        self.assertEqual(replay_band(self.certificate())['leaves'],1)

    def test_wrong_translation_is_rejected(self):
        record=self.certificate(); record['band_target']='10'
        with self.assertRaises(ValueError): replay_band(record)

    def test_wrong_parameter_box_is_rejected(self):
        record=self.certificate(); record['constant_certificate']['type']['ratio_bin']+=1
        with self.assertRaises(ValueError): replay_band(record)


if __name__=='__main__': unittest.main()
