#!/usr/bin/env python3
"""Bind scoped finite checks to the written prefix-hull closure proof.

This is a dependency ledger, not a formal proof assistant.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent/'Freiman_Hall_ray_verification'
def need(ok,msg):
    if not ok:raise ArithmeticError(msg)
def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
normal=read(HERE/'independent_uniform_replay.json');optimized=read(HERE/'independent_uniform_optimized.json')
for result in (normal,optimized):
    need(result['status']=='PASS_INDEPENDENT_UNIFORM_ARITHMETIC','independent arithmetic success')
    for item in result['results']:need(sha(HERE/item['path'])==item['sha256'],'fresh verified certificate identity')
endpoint=read(HERE/'endpoint_returns.json');need(endpoint['status']=='PASS_ALL_INDEX_ENDPOINT_IDENTITIES','endpoint recurrences')
negative=read(HERE/'negative_controls.json');need(negative['status']=='PASS' and len(negative['controls'])==6 and all(r['rejected'] for r in negative['controls']),'six negative controls')
previous=HERE.parent/'structural_replay_20260924'
old=read(previous/'result.json');need(old['status']=='PASS_MATHEMATICAL_GROUPS' and old['source_unchanged'],'previous scoped replay')
groups=read(previous/'logs/replay_summary.json')['groups'];need(len(groups)==12 and all(r['status']=='PASS' for r in groups),'all 12 dependency groups')
manifest=read(PACKAGE/'SHA256SUMS.json');missing=[]
for item in manifest:
    path=PACKAGE/item['path']
    if not path.exists():missing.append(item['path']);continue
    need(sha(path)==item['sha256'],'original dependency changed '+item['path'])
need(missing==['report/Freiman_Hall_ray_report.pdf'],'only known missing PDF')
cost=read(HERE/'verification_cost.json')
result=dict(status='PREFIX_HULL_CLOSURE_WITH_EXISTING_FREIMAN_LEMMAS',
    theorem='For every n>=0, 4+K(3211(313121)^n3)+K(4322(313121)^n) equals its entire convex hull [c_F,b_n].',
    proof_kind='Written mathematical proof plus independently checked finite certificates; not formal proof-assistant verification.',
    proof=dict(path='PREFIX_ROOT_CLOSURE.md',sha256=sha(HERE/'PREFIX_ROOT_CLOSURE.md')),
    new_records=cost['records'],bernstein_coefficients=cost['bernstein_coefficients'],
    coefficient_max_bits=cost['max_saved_coefficient_bits'],coordinate_degree_max=cost['max_coordinate_degree'],
    independent_normal=normal['status'],independent_optimized=optimized['status'],negative_controls=6,
    existing_dependency_groups=[r['group'] for r in groups],
    original_inputs_unchanged=True,missing_delivered_pdf=missing,
    scope_limits=['Uses existing Freiman local selection, history and initial-contact lemmas.',
                  'Does not declare all types in the old exploratory graph filled.',
                  'Does not establish a proof independent of those Freiman lemmas or a historical-machine runtime.'])
(HERE/'closure_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
