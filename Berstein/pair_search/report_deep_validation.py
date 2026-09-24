#!/usr/bin/env python3
"""Check saved deep results and keep global/local precision distinct."""
import hashlib,json
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from deep_validate_replacement import windows,S
ROOT=Path(__file__).resolve().parent

def main():
    source=ROOT/'replacement_cover.json';data=json.loads(source.read_text());local=json.loads((ROOT/'replacement_deep_windows.json').read_text());full=json.loads((ROOT/'replacement_full_4_1e11.json').read_text());points=json.loads((ROOT/'replacement_dense_point_audit.json').read_text())
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    assert local['source_sha256']==full['source_sha256']==digest
    assert len(local['claims'])==len(data['claims'])==11
    assert not points['unresolved'] and len(points['witnesses'])==points['expected']==11080
    count=Counter(w['claim'] for w in points['witnesses'])
    length=Q(0);nodes=0;total=0
    for entry,c in zip(local['claims'],data['claims']):
        expected=windows(c,entry['claim']);actual=[tuple(Q(x)*S for x in w['target_sum']) for w in entry['windows']]
        assert actual==[tuple(v) for v in expected]
        for w in entry['windows']:
            scan=w['scan'];assert scan['complete'] and scan['covers_target'] and scan['exponent']==13
            assert Q(scan['max_width_units'],scan['scale'])<=Q(1,10**13)
            a,b=map(Q,w['target_sum']);assert scan['covered']==[[int(a*S),int(b*S)]]
            length+=b-a;nodes+=scan['visited'];total+=1
    s=full['scan'];assert s['complete'] and s['covers_target'] and Q(s['max_width_units'],s['scale'])<=Q(1,10**11)
    c=data['claims'][3];assert full['target']==c['target']
    assert s['covered']==[[int((Q(str(t))-3)*S) for t in c['target']]]
    text=['# 11候補への追加の数値検証','',
          '**今回の追加検査では新しい穴は検出されなかった。候補の集合・担当区間は変更していない。区間包含の証明ではない。**','',
          '対象は [再探索した11命題](REPLACEMENT_COVER.md)。結果は全区間の検査と局所的な検査を区別する。','',
          '|検査|対象|得られた保証・結果|','|---|---|---|',
          '|既存の全区間検査|11本すべて|担当区間全体で和までの距離 `<=10^-9`|',
          '|今回の全区間検査|第4区間 `[1.171797,1.172072]`|全域で距離 `<=10^-11`。以前より100倍細かい|',
          f'|今回の局所区間検査|全11本に分散した{total}小区間|各小区間の全点で距離 `<=10^-13`|',
          '|今回の点近似|11,080点|全点で誤差 `<10^-30` の合法な周期末尾による表示を有理数で確認|','',
          '**全11区間の全域を `10^-13` で検査したという意味ではない。** 第4区間以外の全域保証は `10^-9` のまま。有限スケールの距離保証から、厳密な包含は従わない。','',
          '## 各行の検査量','',
          '|命題番号|局所検査した小区間数|高精度点近似の数|新しく検出した穴|','|---:|---:|---:|---:|']
    for e in local['claims']:text.append(f"|{e['claim']}|{len(e['windows'])}|{count[e['claim']]}|0|")
    text+=['','## 局所区間の選び方','',
           '- 各担当区間の両端と、17等分した内部の16点。',
           '- 各担当区間の内部から、固定した乱数種で16点を追加。種は `20260924 + 命題番号`。',
           '- これらの点を中心とする幅 `10^-8` の小区間を検査。端点では担当区間内に切り詰める。',
           '- 以前の反例区間と、再探索中に見つかった追加の小さな穴については、両側に `10^-7` 広げた近傍も検査。重なる小区間は合併。','',
           f'小区間の延べ長さは約 `{float(length):.10g}`。局所検査で `{nodes:,}` 個、第4区間の全域検査で `{s["visited"]:,}` 個の円柱対を処理した。対象を選んだ時点から計算まで決定的に再現できる。','',
           '全ての区間検査で整数演算による外向き丸めを使用。第13桁の検査でも幅に丸め分を含めて判定し、オーバーフローや予算切れを成功扱いしていない。全走査が完了した。第13桁のケース・既知の非包含点・オーバーフロー時の失敗を含む24テストが通過した。','',
           '点近似は各担当区間の1001等間隔点（両端を含む）と旧反例の重点検査点。これは局所検査の乱数点とは別の検査である。最後に周期末尾の連分数を有理数で外包し、誤差を再検証した。点数は命題ごとの検査数であり、重複する担当区間に同じ値があれば別に数える。','',
           '## 再実行','',
           '```sh',
           'python3 Berstein/pair_search/deep_validate_replacement.py',
           'python3 Berstein/pair_search/deep_full_interval.py --claim 4 --exponent 11',
           'python3 Berstein/pair_search/audit_rebuilt_cover.py --input Berstein/pair_search/replacement_cover.json --output Berstein/pair_search/replacement_dense_point_audit.json --points 1001',
           'python3 Berstein/pair_search/report_deep_validation.py',
           'python3 -m unittest discover -s Berstein/pair_search -v',
           '```','',
           '- [局所検査の全記録](replacement_deep_windows.json)',
           '- [第4区間の全域検査](replacement_full_4_1e11.json)',
           '- [11,080点の近似表示と有理数誤差](replacement_dense_point_audit.json)',
           '- [局所検査プログラム](deep_validate_replacement.py)',
           '- [任意の命題を全域で再検査するプログラム](deep_full_interval.py)','',
           '全域のさらなる精密化を実行する場合は最後のプログラムの `--claim` と `--exponent` を指定する。ただし幅の広い区間は計算量が大きくなる。今回の結果は、未検査の場所やさらに小さいスケールで穴がないことまで保証しない。','']
    (ROOT/'DEEP_VALIDATION.md').write_text('\n'.join(text))
    print('Verified:',total,'windows;',nodes,'local nodes;',len(points['witnesses']),'point witnesses; total window length',float(length))
if __name__=='__main__':main()
