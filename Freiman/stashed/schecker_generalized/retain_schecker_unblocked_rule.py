#!/usr/bin/env python3
"""Replay the explicit rollback and preserve the unblocked Schecker rule.

Run from the repository root. This checks input identity by saved game keys,
replays counterexamples, and audits all retained local implications.
"""
import json,copy,sys
from pathlib import Path
sys.path.insert(0,str(Path('Freiman/schecker_generalized').resolve()))
from hybrid_discovery import Constructive
from repair_root_point_gap import bank_entry,known_gap_hits
from search_piecewise_charts import fingerprint
from verify_piecewise_charts import PiecewiseVerifier
from chart_strategy_ranks import report
D=Path('Freiman/schecker_generalized')
saved=json.loads((D/'schecker_unbalanced_returns_20260924.state.json').read_text());before=json.loads((D/'schecker_fragment_return_20260924.state.json').read_text())
# Game keys retain identity across these extensions. Only the second new rule
# is rolled back to its original pending obligation; the root interval stays.
if saved['game']['keys'][3026]!=before['game']['keys'][3026]:raise ValueError('rollback key mismatch')
saved['game']['entries'][3026]=copy.deepcopy(before['game']['entries'][3026])
if saved['game']['entries'][3026]['status']!='pending':raise ValueError('expected pending original obligation')
bank=saved['gap_filter_bank']
for name,probefile in [('schecker_balance_control_20260924','schecker_balance_children_probe_20260924'),('schecker_unbalanced_returns_20260924','schecker_long_memory_children_probe_20260924')]:
 checker=PiecewiseVerifier(json.loads((D/(name+'.json')).read_text()))
 probes=json.loads((D/(probefile+'.json')).read_text())
 for row in probes['rows']:
  if row['witness']:
   entry=bank_entry(checker,row['witness'])
   if entry not in bank:bank.append(entry)
lane=Constructive(saved);graph=lane.graph();checker=PiecewiseVerifier(graph);audit=checker.audit()
if audit['failed_rules']:raise ValueError('rollback audit failed')
state=lane.search.snapshot(lane.game,lane.config,fingerprint());state['gap_filter_bank']=bank
retained_index=sorted(lane.game.reachable()).index(3008)
newchildren=checker.local(retained_index)['dependencies']
hits=known_gap_hits(checker,newchildren,bank)
if hits:raise ValueError('newly retained children refuted')
try:closure=checker.closed()
except ValueError as error:closure=dict(closed=False,reason=str(error))
result=dict(status='Schecker induction remains open; no Freiman filling lemma used',rolled_back_game_node=3026,
            retained_game_node=3008,retained_children=newchildren,gap_filters=len(bank),known_gap_hits=hits,
            ranks=report(graph),verified_local_rules=len(audit['verified_rules']),open_nodes=len(audit['open_nodes']),closure=closure)
for path,data in [('schecker_return_current_20260924.state.json',state),('schecker_return_current_20260924.json',graph),
 ('schecker_return_current_20260924.audit.json',audit),('schecker_return_current_20260924.report.json',result)]:
 (D/path).write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps(result,indent=2))
