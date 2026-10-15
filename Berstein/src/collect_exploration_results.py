"""Collect completed proof checks and bounded search outcomes without conflation."""
import hashlib
import json
from pathlib import Path
from fractions import Fraction as Q

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'Berstein/data'


def checked_report(name):
    path=DATA/name
    report=json.loads(path.read_text())
    assert report['passed'],name
    for filename,digest in report.get('sha256',{}).items():
        assert hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()==digest,filename
    return report


def main():
    positive=checked_report('interval_extensions_verified.json')
    bulk=checked_report('exploration_bulk_bounds.json')
    controls=checked_report('exploration_bounded_controls.json')
    checked_report('exploration_kernel_controls.json')
    checked_report('exploration_parallel_equivalence.json')
    audits={name:checked_report(name+'_input_audit.json') for name in
            ['avoid313_m2','avoid_alt5_m2','avoid_alt5_return10',
             'avoid_alt5_return10_unrestricted','avoid_alt5_spine10']}
    search=json.loads((DATA/'avoid_alt5_spine10.json').read_text())
    if search['closed_family_found']:
        assert search['surviving_states']>0 and not search['round_limit_reached']
        status='closed_family_found'
    elif search['surviving_states']==0:
        status='specified_finite_family_empty'
    else:
        assert search['round_limit_reached']
        status='UNKNOWN_at_round_limit'
    small=json.loads((DATA/'avoid313_m2.json').read_text())
    assert small['surviving_states']==0 and not small['closed_family_found']
    output=dict(passed=True,extended_interval=positive['claim'],
                rational_components=positive['rational_components'],
                global_maximality_proved=False,
                experimental_languages=[
                    dict(language='313',status='specified_finite_family_empty',
                         initial_rows=2913408,completed_rounds=len(small['round_counts'])),
                    dict(language='31313,13131',spine_depth=10,
                         initial_rows=6078592,round_limit=80,status=status,
                         remaining_rows=search['surviving_states'],
                         completed_rounds=len(search['round_counts']))],
                interval_in_berstein_region_proved=False,
                conditional_root=bulk['results'][1]['conditional_root'],
                input_audits_passed=list(audits),
                bounded_status_controls=len(controls['cases']),
                interpretation='An empty finite sufficient family or a budget stop is not a nonexistence theorem.')
    lower=DATA/'lower_interval_verified.json'
    if lower.exists():
        lower_report=checked_report(lower.name)
        output['interval_in_berstein_region_proved']=lower_report['interval_in_berstein_region_proved']
        output['lower_interval']=lower_report
        pieces=[tuple(map(Q,iv)) for iv in positive['rational_components']+lower_report['rational_components']]
        joined=[]
        for a,b in sorted(pieces):
            if joined and a<=joined[-1][1]:joined[-1]=(joined[-1][0],max(joined[-1][1],b))
            else:joined.append((a,b))
        original=Q('4.52578'),Q('4.52754')
        extended=next((a,b) for a,b in joined if a<=original[0]<original[1]<=b)
        output['combined_rational_components']=[[str(v) for v in iv] for iv in joined]
        output['original_interval_extended_to']=[str(v) for v in extended]
        output['original_interval_extended_to_decimal']=[float(v) for v in extended]
        output['original_31313_result']=output['extended_interval']
        output['extended_interval']=f'[{float(extended[0]):.8f},{float(extended[1]):.8f}] subset L and M below c_F'
        output['original_interval_width_ratio']=str((extended[1]-extended[0])/(original[1]-original[0]))
        output['original_interval_width_increase_percent']=float(((extended[1]-extended[0])/(original[1]-original[0])-1)*100)
    paths=[DATA/'interval_extensions_verified.json',DATA/'exploration_bulk_bounds.json',
           DATA/'avoid313_m2.json',DATA/'avoid_alt5_spine10.json',
           ROOT/'Berstein/src/exploration_kernel.cpp',Path(__file__).resolve()]
    if lower.exists():paths.append(lower)
    output['sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (DATA/'interval_exploration_summary.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k not in ('sha256','conditional_root','lower_interval')},indent=2))


if __name__=='__main__':main()
