#!/usr/bin/env python3
"""Replay mathematical groups without claiming missing-PDF/package validation.

Original arithmetic and its declared input transformations are copied unchanged.
Only the absent delivered report PDF is omitted; any other missing/changed input
is fatal. Assembly/PDF identity is explicitly outside this replay's scope.
"""
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys, tempfile, time

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent / 'Freiman_Hall_ray_verification'
sys.path.insert(0, str(PACKAGE / 'verification'))
from check_manifest import inventory, safe, sha
from replay import heading_normalization
from printed_source import normalize_bytes

GROUPS = ['global_selection', 'initial', 'foundations_upper', 'section14',
          'section15', 'terminal', 'late', 'j_family', 'targets_bridges',
          'suffix_histories', 'middle', 'translation']

def dump(name, obj):
    (HERE / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

def main():
    expected = {r['path']: {k:r[k] for k in ('bytes','sha256')}
                for r in json.loads((PACKAGE/'SHA256SUMS.json').read_text())}
    actual = inventory(PACKAGE)
    diff = dict(missing=sorted(expected.keys()-actual.keys()),
                extra=sorted(actual.keys()-expected.keys()),
                changed=sorted(k for k in expected.keys()&actual.keys()
                               if expected[k] != actual[k]))
    dump('source_inventory.json', dict(differences=diff, matched_files=len(expected.keys()&actual.keys()),
         manifest_sha256=sha(PACKAGE/'SHA256SUMS.json')))
    if diff['missing'] != ['report/Freiman_Hall_ray_report.pdf'] or diff['changed'] or any(
            Path(n).name != '.DS_Store' for n in diff['extra']):
        raise ValueError('Unexpected source inventory differences')
    work = Path(tempfile.mkdtemp(prefix='freiman-math-replay-'))
    records=[]; targets=set()
    for row in json.loads((PACKAGE/'verification/execution_layout.json').read_text())['files']:
        src=PACKAGE/safe(row['source']); dst=work/safe(row['target'])
        if row['target'] in targets: raise ValueError('Duplicate target')
        targets.add(row['target'])
        if not src.exists():
            if row['source'] != diff['missing'][0] or row['role'] != 'report_pdf':
                raise ValueError('Missing mathematical input')
            continue
        data=src.read_bytes()
        key=row.get('normalization_key')
        if key is not None:
            if row['role']!='printed_certificate' or row['source']!='report/source/'+key:
                raise ValueError('Invalid normalization role')
            data=normalize_bytes(key,data,PACKAGE/'verification/print_normalization.json')
        transform=row.get('transform')
        if transform=='plain_table_columns': data=data.replace(b'>{\\raggedright\\arraybackslash}',b'')
        elif transform is not None: raise ValueError('Unknown transform')
        if row.get('heading_replacements'):
            if row['role']!='printed_certificate': raise ValueError('Invalid heading role')
            data=heading_normalization(data,row['heading_replacements'])
        dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(data)
        records.append(dict(source=row['source'],target=row['target'],source_sha256=sha(src),
                            execution_sha256=hashlib.sha256(data).hexdigest()))
    dump('execution_inputs.json',records)
    result=dict(status='RUNNING', scope='Mathematical certificate groups only; not complete package or PDF verification',
                groups=GROUPS, execution_tree=str(work), python=sys.version)
    dump('result.json',result)
    start=time.monotonic()
    env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None)
    try:
        result['returncode']=subprocess.call([sys.executable,'-B',str(work/'work/release_tools/replay_all.py'),
            '--groups',*GROUPS,'--workers','1'],cwd=work,env=env)
        if inventory(PACKAGE)!=actual: raise ValueError('Source package changed')
        result['source_unchanged']=True
        result['status']='PASS_MATHEMATICAL_GROUPS' if result['returncode']==0 else 'FAIL'
    finally:
        result['seconds']=round(time.monotonic()-start,3)
        if (work/'replay_logs').exists(): shutil.copytree(work/'replay_logs',HERE/'logs',dirs_exist_ok=True)
        dump('result.json',result)
    return result['returncode']

if __name__=='__main__': raise SystemExit(main())
