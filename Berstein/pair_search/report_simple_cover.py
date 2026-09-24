#!/usr/bin/env python3
"""Render the compact definitions after all final audits have passed."""
import hashlib,json
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from audit_simple_cover import verify
ROOT=Path(__file__).resolve().parent

def dec(x):return f'{float(Q(x)):.10f}'.rstrip('0').rstrip('.')
def main():
 source=ROOT/'simple_cover.json';data=json.loads(source.read_text());verify(data)
 pts=json.loads((ROOT/'simple_cover_points_audit.json').read_text());loc=json.loads((ROOT/'simple_cover_local_audit.json').read_text());sha=hashlib.sha256(source.read_bytes()).hexdigest()
 assert pts['source_sha256']==loc['source_sha256']==sha and not pts['unresolved']
 assert len(loc['claims'])==len(data['claims'])==11
 nw=0
 for e in loc['claims']:
  for w in e['windows']:
   s=w['scan'];assert s['complete'] and s['covers_target'] and s['exponent']==13
   assert Q(s['max_width_units'],s['scale'])<=Q(1,10**13);nw+=1
 old=json.loads((ROOT/'replacement_cover.json').read_text())
 oldn=sum(len(d['forbidden']) for d in old['definitions']);newn=sum(len(d['forbidden']) for d in data['definitions']);maxn=max(len(d['forbidden']) for d in data['definitions'])
 lines=['# 単純な定義を優先した11本のGauss–Cantor和の候補','',
 '**11本・10種類の基本集合で `[4.1,4.52]` を覆う包含候補を構成した。禁止語の総数は '+str(oldn)+' 個から '+str(newn)+' 個、1集合の最大数は17個から '+str(maxn)+' 個へ減少。K_F+K_F そのものも組み込んだ。全て未証明の包含命題であり、有限スケールの距離保証とは区別する。**','',
 '## 基本集合の簡潔な定義','',
 '数字は全て `{1,2,3}`。下表の「種語」とその逆順を禁止する。回文は1個と数える。例えば種語 `2313` は `2313` と `3132` の両方の禁止を意味する。A,…,I はこのレポート内の記号で、以前のレポートとは異なる。','',
 '|集合|禁止する種語（逆順も禁止）|実際の禁止語数|','|---|---|---:|']
 for d in data['definitions']:
  ws=d['forbidden'];seeds=sorted({min(w,w[::-1]) for w in ws},key=lambda w:(len(w),w))
  assert set(ws)==set(seeds)|{w[::-1] for w in seeds}
  label='K_F' if d['label']=='KF' else d['label']
  lines.append('|'+label+'|'+', '.join('`'+w+'`' for w in seeds)+'|'+str(len(ws))+'|')
 lines+=['','この表示では各集合に必要な独立な禁止規則は1〜5組。特に E は `131,313` の2語だけ、K_F は `131` の1語だけ。I はさらに `a131b (a,b∈{2,3})` の禁止という1つのパターンでも定義できる。最も長い禁止語は7桁のままであり、全てを K_F と同程度の1語にできたわけではない。','',
 '## 証明すれば十分な11本','',
 '`X[u,v,…]` はそれらの接頭語の円柱の合併。B,C については','',
 '`Σ_X = X[11,12] ∪ (X[2] ∖ X[2312])`','',
 'と略記する。B,C では `2313` が禁止されるので、これは正確に `X[11,12,21,22,2311,232,233]` と等しい。短い表記にしただけで条件を変えていない。各行の左右は独立に選ぶ。','',
 '|番号|左辺 K+L|含ませたい区間 I|','|---:|---|---|']
 for c in data['claims']:
  def factor(side):
   if c['label']=='KF' and c[side]==['']:return 'K_F'
   if c['label'] in ['B','C'] and c[side]==['11','12','21','22','2311','232','233']:return 'Σ_'+c['label']
   return c['label']+'['+','.join(c[side])+']'
  a,b=[Q(str(x))-3 for x in c['target']]
  lines.append(f"|{c['claim']}|`{factor('left')} + {factor('right')}`|`[{dec(a)}, {dec(b)}]`|")
 lines+=['','これらの I は正の重なりを持って `[1.1,1.52]` 全体を覆う。各行について中央以外のPerron値の上界が `3+inf I` より小さいことを有理数で検証した。逆順対称性と全状態から周期2への合法な接続を使う帰着により、**全11本が成立すれば `[4.1,4.52] ⊂ L` が従う。**','',
 '特に第9命題は文字どおり `K_F+K_F ⊇ [1.27,1.36]`。第8命題の担当区間を短くしてこれを挿入し、後半2命題を同じ単純な集合 H にまとめたため、命題数は11本を維持した。','',
 '## 全交差組の支配条件','',
 '|番号|中央以外の有理数上界（小数表示）|中央の目標下端|','|---:|---:|---:|']
 for c in data['claims']:lines.append(f"|{c['claim']}|{float(Q(c['dominance_bound'])):.12f}|{dec(c['target'][0])}|")
 lines+=['','小数は表示用。計算・比較には [JSON](simple_cover.json) の正確な有理数を使用した。背景窓は半径4、末尾の外包は16回の有理数反復で評価し、短い接頭語は合法な長さ4の接頭語へ全て展開して中央近傍を検査した。','',
 '## 数値検証','',
 '- **全11区間:** それぞれ全点で和集合までの距離 `<=10^-9`。新しい小集合については全区間を再走査した。変更していない集合の区間短縮や、検査済み部分積の統合では、厳密な包含関係から既存の被覆を移した。',
 f'- **局所検査:** 新しい集合について{nw}小区間を全域で `<=10^-13` まで細分。端点、等間隔点、固定乱数点、旧反例、今回棄却した単純化案の穴の周辺を含む。全走査完了・被覆成功。',
 f'- **高精度点近似:** {len(pts["witnesses"]):,}点で誤差 `<10^-30` の周期末尾の表示を構成し、有理数で再検証。未解決点0。',
 '- 数値検証に新しい反例は残らなかったが、全スケールの区間包含は未証明。局所 `10^-13` を全域の保証と読み替えることはできない。',
 '- 一部の局所走査は最初の計算予算を超えたため、予算を増やして完了させた。予算切れを穴や成功と扱っていない。','',
 '## 探索の範囲と変更','',
 '少数の短い禁止語を持つ既存の候補群を比較し、長い禁止語を短い部分語の禁止へ置き換えた。後者は集合を小さくするため、古い数値被覆を引き継げず、必ず再走査した。粗い `10^-7` で通って `10^-9` で穴が出る案は採用していない。最後に円柱の指定を緩めることも試したが、新しい交差組の支配条件を維持できる場合だけ許した。','',
 'これは探索範囲内での簡略化であり、全てのGauss–Cantor集合に対する最小性の証明ではない。集合の数は増やさず、長い禁止語の数と定義の重複を減らした。','',
 '## 記録と再実行','',
 '- [最終11命題・完全な禁止語・有理数上界・被覆](simple_cover.json)',
 '- [点近似と有理数誤差](simple_cover_points_audit.json)',
 '- [局所区間の検査記録](simple_cover_local_audit.json)',
 '- [短い規則の探索](short_rule_search.py)',
 '- [最終的な区間分担・統合の検査](finalize_simple_cover.py)',
 '- [最終集合での独立した再評価](audit_simple_cover.py)','',
 '保存済みの全域走査から最終結果を再構築するには:','',
 '```sh',
 'python3 Berstein/pair_search/finalize_simple_cover.py',
 'python3 Berstein/pair_search/audit_simple_cover.py points',
 'python3 Berstein/pair_search/audit_simple_cover.py local',
 'python3 Berstein/pair_search/report_simple_cover.py',
 '```','',
 '全域の新しい走査自体を再実行するスクリプトは `refine_simple_choices.py`, `refine_short_choices.py`, `refine_last_short_choices.py`。探索途中の失敗候補も保存した。集約被覆の再評価と全葉の再走査は別であり、後者にはこれらの再実行が必要。','']
 (ROOT/'SIMPLE_COVER.md').write_text('\n'.join(lines));print('Final report:',len(data['claims']),'claims',len(data['definitions']),'sets',oldn,'->',newn,'rules;',nw,'windows;',len(pts['witnesses']),'points')
if __name__=='__main__':main()
