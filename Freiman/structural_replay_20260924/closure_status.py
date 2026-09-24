#!/usr/bin/env python3
"""Summarize fresh scoped results; never infer new-proof closure from tests."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent

def read(p):return json.loads(p.read_text()) if p.exists() else None
run=read(HERE/'result.json') or {}
progress=read(HERE/'logs/replay_summary.json')
if not progress and run.get('execution_tree'):
    rows=read(Path(run['execution_tree'])/'replay_logs/progress.json') or []
else:rows=(progress or {}).get('groups',[])
by_name={r['group']:r for r in rows}
groups={g:by_name.get(g,{}).get('status','PENDING') for g in run.get('groups',[])}
checks={}
for name,file in [('generic_history','history_crosscheck.json'),('entry_history','check_entry_dag.json'),
                  ('joint_history','check_joint_dag.json'),('C89_graph','history_c_crosscheck.json'),('parameter_recurrences','check_parameter_inductions.json'),
                  ('root_interface','root_interface.json'),('short_parent','short_parent_replay/replay_result.json')]:
    value=read(HERE/file);checks[name]=value.get('status','NO_STATUS') if value else 'PENDING'
result=dict(status='NEW_SCHECKER_INDUCTION_NOT_CLOSED',structural_checks=checks,
    existing_Freiman_certificate_groups=groups,mathematical_replay_status=run.get('status','NOT_STARTED'),
    passed_groups=sum(v=='PASS' for v in groups.values()),total_groups=len(groups),
    missing_new_proof_connections=[
        'Express carried-target and selection-priority hypotheses in the new induction checker.',
        'Prove the connection of its requested initial intervals to the replacement selection system.'
    ],complete_package_validation='NOT_RUN_MISSING_DELIVERED_PDF',
    note='The Freiman report contains the existing all-depth proof. Finite replay and the small structural graphs do not themselves close the separate Schecker search graph.')
(HERE/'closure_status.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
