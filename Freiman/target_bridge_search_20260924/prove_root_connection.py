#!/usr/bin/env python3
"""Uniform contacts joining the old lower initial system to the new upper strip."""
from pathlib import Path
import json
from uniform_restart_strip import Proof,need
HERE=Path(__file__).resolve().parent
cases=[]
for zero in (True,False):
    p=Proof(zero,True,core=True)
    root=('3','');upper_entry=('33','11')
    p.good(root);p.good(upper_entry)
    # A(n,2) has even/even physical prefixes (3211 S^n 3133,4322 S^n 33).
    # Its raw H upper endpoint appends 1213 to each, with tail overline12.
    h_upper=('31331213','331213')
    p.comparison('lower_initial_to_root',h_upper,p.endpoint(root,'lo'))
    p.comparison('root_to_upper_strip',p.endpoint(root,'hi'),p.endpoint(upper_entry,'lo'))
    p.comparison('root_to_upper_strip_reverse',p.endpoint(upper_entry,'hi'),p.endpoint(root,'lo'))
    row=dict(n_zero=zero,chain=[root,upper_entry],records=p.records,
             positive=all(r['positive'] for r in p.records))
    cases.append(row);print('n_zero',zero,'positive',row['positive'],'records',len(row['records']),flush=True)
(HERE/'uniform_root_connection.json').write_text(json.dumps(dict(
    status='UNIFORM_ROOT_CONTACTS_PROVED' if all(r['positive'] for r in cases) else 'OPEN',
    box=['0 <= x <= 1/85','y unused'],cases=cases,
    scope='All-n restart goodness and contacts; lower subsystem and restart theorem are written proof dependencies'),indent=2)+'\n')
