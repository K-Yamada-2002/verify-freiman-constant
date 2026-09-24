#!/usr/bin/env python3
"""Render the final report only after checking all saved evidence agrees."""
import json
from fractions import Fraction as Q
from pathlib import Path
from verify_reduced import inspect
ROOT=Path(__file__).resolve().parent

def decimal(q):
    return f'{float(q):.12f}'.rstrip('0').rstrip('.')

def main():
    data=json.loads((ROOT/'replacement_cover.json').read_text());models,defs,claims=inspect(data)
    points=json.loads((ROOT/'replacement_point_audit.json').read_text());stress=json.loads((ROOT/'replacement_stress_1e12.json').read_text())
    assert not points['unresolved'] and points['definitions']==defs
    for a,b in zip(points['claims'],claims):
        for key in ('claim','label','left','right','target','dominance_bound'):assert a[key]==b[key]
    assert all(Q(c['maximum_width'])<=Q(1,10**9) for c in claims)
    assert all(x['scan']['complete'] and x['scan']['covers_target'] and x['scan']['exponent']==12 for x in stress['neighborhoods'])
    text=['# 再探索した11本のGauss–Cantor和の包含候補','',
          '**以下の11本の包含がすべて成立すれば `[4.1,4.52] ⊂ L` が従う。全11本について、担当区間の全点で和集合までの距離 `10^-9` 以下を整数・有理数演算で検証した。包含自体は未証明。**','',
          '旧10本に見つかった反例は取り消していない。担当区間を分割し、基本集合や円柱を変更した新しい候補である。下記の A,… の記号はこのレポート内だけの定義で、旧レポートの記号とは対応しない。','',
          '## 証明対象','',
          '`X[u,v,…]` は、X の中でいずれかの接頭語を持つ連分数の集合。各行は左右を独立に選ぶ完全な直積の和である。区間 I は和の値であり、Lagrangeスペクトルの値には3を足す。','',
          '|番号|K|L|含ませたい区間 I|','|---:|---|---|---|']
    for c in claims:
        factor=lambda side:c['label']+'['+','.join(c[side])+']'
        text.append(f"|{c['claim']}|`{factor('left')}`|`{factor('right')}`|`[{decimal(Q(c['target'][0]))}, {decimal(Q(c['target'][1]))}]`|")
    text+=['','これらの区間は正の重なりを持って `[1.1,1.52]` 全体を覆う。命題数は11本、基本集合は'+str(len(defs))+'種類。最小本数の主張ではない。','',
           '## 基本集合の完全な定義','',
           '全ての数字は `{1,2,3}`。各集合は、次の禁止語を一度も含まない無限連分数 `[0;a₁,a₂,…]` 全体。','',
           '|集合|禁止語|','|---|---|']
    for d in defs:text.append('|'+d['label']+'|'+', '.join('`'+w+'`' for w in d['forbidden'])+'|')
    text+=['','禁止語のオートマトンと、半径 r の窓のPerron上界で定めた元のグラフについて、許容言語の完全一致を有限状態対の走査で確認した。禁止語を短いサンプルから推測したものではない。','',
           '## なぜこの11本で十分か','',
           '各行で、中央に3を置いた列の中央以外のPerron値を有理数で上から評価した。背景窓と、左右の全交差組に対する中央近傍の双方を検査している。','',
           '|番号|中央以外の共通上界（外向き丸め）|中央に含ませたい区間の下端|','|---:|---:|---:|']
    for c in claims:
        q=Q(c['dominance_bound']);bound=Q(-(-(q*10**9).numerator//(q*10**9).denominator),10**9)
        text.append(f"|{c['claim']}|{decimal(bound)}|{decimal(3+Q(c['target'][0]))}|")
    text+=['','全行で上界は右列より真に小さい。全状態から周期2へ合法に接続でき、グラフは反転対称なので、左右の長いブロックを長い2の列でつなげられる。中央の値を `3+x+y` に収束させ、その他の値をこの上界以下に抑える標準のPerron構成により、担当区間内の実際の和はLagrangeスペクトルに入る。詳しい構成は [帰着の議論](README.md#lagrange-スペクトルへの帰着条件)。従って表の11本の区間包含を証明すれば、目標区間全体の包含が従う。','',
           '## 数値的な裏付け','',
           '- **全区間:** 各行ごとに、非空な円柱対の外包を幅 `10^-9` 以下に細分。全ての担当区間を覆った。サンプル点だけの検査ではない。',
           '- **旧反例周辺:** '+str(len(stress['neighborhoods']))+'個の小区間を、それぞれ全域で幅 `10^-12` 以下まで細分して被覆。旧反例の近傍に残った穴も、最終候補では検出されなかった。',
           '- **高精度点近似:** 端点・等間隔点・旧反例区間の内部など計'+str(len(points['witnesses']))+'点で、合法な周期2末尾の表示を構成し、誤差 `<10^-30` を有理数で再検証。未解決点は0。',
           '- **判定:** 全区間の細分器は外向き丸めを伴う整数演算。128ビット演算のオーバーフローは失敗として扱う。距離保証は、各採用外包が実際の和の点を含むことによる。',
           '- **整理の正当性:** 第2行は、途中候補で穴が見つかった位置より手前に担当区間を縮めた。第3行がその先を別の集合で覆う。第10行は同じ基本集合による2組を統合し、新しく加わる全交差組の支配条件も検査した。','',
           '今回も有限スケールに限る検査であり、`10^-9` より小さい穴が他の場所に存在しないことは示していない。以前の候補に反例が出たことを踏まえ、「包含が正しい」と断定するものではない。','',
           '## データと再実行','',
           '- [最終11命題・有理数の支配上界・被覆](replacement_cover.json)',
           '- [高精度点近似の証拠](replacement_point_audit.json)',
           '- [旧反例周辺の10^-12検査](replacement_stress_1e12.json)',
           '- [元の10^-9走査](rebuilt_cover.json): 途中の第2行には穴があり、その区間全体を採用していない。',
           '- [追加の第3行の走査](research_second_split.json)',
           '- [最終的な切り詰め・追加・統合](finalize_replacement.py)','',
           '既存の探索データを使って最終検査を再実行するには、リポジトリのルートから:','',
           '```sh',
           'python3 Berstein/pair_search/rebuild_cover.py --exponent 9',
           'python3 Berstein/pair_search/research_cover.py --radius 3 --claims 1 --first-lo 4.161580 --exponent 9 --output Berstein/pair_search/research_second_split.json',
           'python3 Berstein/pair_search/finalize_replacement.py',
           'python3 Berstein/pair_search/stress_replacement_cover.py --input Berstein/pair_search/replacement_cover.json',
           'python3 Berstein/pair_search/audit_rebuilt_cover.py --input Berstein/pair_search/replacement_cover.json --output Berstein/pair_search/replacement_point_audit.json',
           'python3 Berstein/pair_search/write_replacement_report.py',
           '```','',
           '細分の全葉は実行中に検査し、集約被覆と最大幅を保存する。保存された集約値だけを読む検査は全葉の再走査とは異なる。上記の実行で全葉を再生成できる。探索の失敗データも残し、成功した候補と区別した。','']
    (ROOT/'REPLACEMENT_COVER.md').write_text('\n'.join(text))
    print('Report written:',len(claims),'claims',len(defs),'sets',len(points['witnesses']),'witnesses')
if __name__=='__main__':main()
