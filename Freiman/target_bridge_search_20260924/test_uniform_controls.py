from pathlib import Path
import copy,json,tempfile,unittest
import verify_uniform_restart as v
HERE=Path(__file__).resolve().parent
class Controls(unittest.TestCase):
    def test_certificate_mutations_rejected(self):
        source=json.loads((HERE/'uniform_periodic_strip.json').read_text())
        def missing_case(d):d['cases'].pop()
        def missing_record(d):d['cases'][0]['records'].pop(0)
        def wrong_sign(d):d['cases'][0]['records'][0]['bernstein'][0]=['-1','0','0','0']
        def wrong_anchor(d):d['cases'][0]['chain'][-1][1]+='1'
        def duplicate_monomial(d):d['cases'][0]['records'][0]['polynomial'].append(copy.deepcopy(d['cases'][0]['records'][0]['polynomial'][0]))
        def false_mode(d):
            row=next(r for r in d['cases'][0]['records'] if r['name']=='auxiliary_cut');row['meta']['short']=not row['meta']['short']
        results=[]
        for mutation in (missing_case,missing_record,wrong_sign,wrong_anchor,duplicate_monomial,false_mode):
            with self.subTest(mutation=mutation.__name__),tempfile.TemporaryDirectory() as tmp:
                data=copy.deepcopy(source);mutation(data);path=Path(tmp)/'bad.json';path.write_text(json.dumps(data))
                with self.assertRaises(ArithmeticError):v.verify_file(path,False)
                results.append(dict(mutation=mutation.__name__,rejected=True))
        (HERE/'negative_controls.json').write_text(json.dumps(dict(status='PASS',controls=results),indent=2)+'\n')
if __name__=='__main__':unittest.main()
