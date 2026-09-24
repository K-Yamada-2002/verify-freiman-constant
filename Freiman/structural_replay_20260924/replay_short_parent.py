#!/usr/bin/env python3
"""Fresh supplementary replay of the short-parent exception and its bindings.

Uses the original execution preparation and mathematical programs unchanged.
The missing PDF/complete-package gate is not claimed by this scoped replay.
"""
from pathlib import Path
from types import SimpleNamespace
import json,sys
HERE=Path(__file__).resolve().parent
work=Path(json.loads((HERE/'result.json').read_text())['execution_tree'])
sys.path.insert(0,str(work/'verification'))
from replay_revision import RevisionReplay
args=SimpleNamespace(package=work,output=HERE/'short_parent_replay',stages=[],preflight=False,
                     workers=1,timeout=0,keep_work=True)
r=RevisionReplay(args)
r.summary['interpretation']='Scoped short-parent and late-J finite verification only. No PDF or complete-package validation.'
r.summary['requested_modules']=['late_j','global']
try:
    r.prepare()
    for module in ('late_j','global'):r.run_module(module)
    r.summary['status']='PASS_SCOPED_SHORT_PARENT_CHECKS'
except BaseException as exc:
    r.summary['status']='FAIL';r.summary['error']=repr(exc);raise
finally:r.save()
