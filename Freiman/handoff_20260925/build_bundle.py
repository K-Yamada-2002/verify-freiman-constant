#!/usr/bin/env python3
"""Snapshot all Schecker source/history files, excluding caches, with hashes."""
from pathlib import Path
import hashlib,io,json,tarfile
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'schecker_generalized'
PREFIX='schecker_handoff_20260925'
ARCHIVE=HERE/(PREFIX+'.tar.gz')
verify=b'''from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'SHA256SUMS.json').read_text())
for row in manifest['files']:
    path=root/row['path']
    data=path.read_bytes()
    if len(data)!=row['bytes'] or hashlib.sha256(data).hexdigest()!=row['sha256']:
        raise SystemExit('MISMATCH: '+row['path'])
print('PASS: %d snapshot files; this is file integrity, not proof closure.' % len(manifest['files']))
'''
readme='''Schecker型証明探索の移行スナップショット（2026-09-25）

証明は未完成です。現在の正本は3,176型・1,183局所規則・1,993未解決。

1. このディレクトリで python3 VERIFY_BUNDLE.py を実行する。
2. schecker_generalized/HANDOFF_20260925.md を読む。
3. cd schecker_generalized
4. python3 -B check_handoff_20260925.py --output /tmp/schecker-handoff-replay.json
5. 文書の手順でC++発見器を再ビルドし、正本のstateから別名へ出力して続行する。

このアーカイブは未コミットのコードと保存状態も含む作業ツリーのスナップショット。
__pycache__等のキャッシュは除外。既存Freiman原本・Berstein全体は収録していない。
背景資料へのディレクトリ外リンクは元リポジトリで参照すること。
'''.encode()
extras={'VERIFY_BUNDLE.py':verify,'README.txt':readme}
files=[p for p in sorted(SOURCE.rglob('*')) if p.is_file() and not p.is_symlink()
       and '__pycache__' not in p.parts and p.suffix in {'.py','.cpp','.md','.json','.log'}]
rows=[]
for p in files:
    data=p.read_bytes();rows.append(dict(path='schecker_generalized/'+p.relative_to(SOURCE).as_posix(),bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
for name,data in extras.items():rows.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
manifest=dict(date='2026-09-25',scope='Schecker source, reports and saved states; proof remains open',files=rows)
encoded=(json.dumps(manifest,indent=2)+'\n').encode()
(HERE/'SHA256SUMS.json').write_bytes(encoded)
with tarfile.open(ARCHIVE,'w:gz',compresslevel=6) as archive:
    for row in rows:
        name=row['path'];data=extras[name] if name in extras else (SOURCE/Path(name).relative_to('schecker_generalized')).read_bytes()
        if hashlib.sha256(data).hexdigest()!=row['sha256']:raise ValueError('source changed during packaging: '+name)
        entry=tarfile.TarInfo(PREFIX+'/'+name);entry.size=len(data);entry.mode=0o644
        archive.addfile(entry,io.BytesIO(data))
    entry=tarfile.TarInfo(PREFIX+'/SHA256SUMS.json');entry.size=len(encoded);entry.mode=0o644
    archive.addfile(entry,io.BytesIO(encoded))
# Verify every archived payload, without extraction or executing archive content.
with tarfile.open(ARCHIVE,'r:gz') as archive:
    members=archive.getmembers()
    if {m.name for m in members}!={PREFIX+'/'+r['path'] for r in rows}|{PREFIX+'/SHA256SUMS.json'}:raise ValueError('archive inventory mismatch')
    for row in rows:
        stream=archive.extractfile(PREFIX+'/'+row['path']);digest=hashlib.sha256();size=0
        while chunk:=stream.read(1024*1024):digest.update(chunk);size+=len(chunk)
        if size!=row['bytes'] or digest.hexdigest()!=row['sha256']:raise ValueError('archive hash mismatch')
result=dict(archive=ARCHIVE.name,sha256=hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),bytes=ARCHIVE.stat().st_size,
            payload_files=len(rows),uncompressed_bytes=sum(r['bytes'] for r in rows),status='PASS_ARCHIVE_HASH_REPLAY')
(HERE/'BUNDLE_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
