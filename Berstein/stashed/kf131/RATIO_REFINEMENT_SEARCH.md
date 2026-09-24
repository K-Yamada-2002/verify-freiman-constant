# 到着する比率の範囲だけを子の型で受ける

2026-09-22。[前回](FEEDBACK_CLOSURE_SEARCH.md)の53,954型のグラフから探索を継続した。
今回は、固定されていた比率の箱を、必要箇所で二分・四分・八分する機能を追加した。
閉じた証明書はまだ得られていない。実行集計は [ratio_search_report.json](ratio_search_report.json)。
比較用の従来版1設定を含む10設定を実行した。

## 1. 過大な帰納義務を減らす

以前は、後続の比率の像がある箱 `H` の一部 `H'` にしか入らなくても、
子の区間 `J` を箱 `H` 全体で埋める型を要求していた。
`H\H'` のパラメータで `J` に穴があれば、その子は不要な条件のために使えなくなる。

新方式では、実際に必要な範囲 `H'` を記録し、その範囲を覆う小箱だけを子に使える。
必要な範囲が二つの小箱をまたぐ場合は、両方の子の義務を残す。
粗い箱で受ける方法も残している。

保存済みグラフの未解決42,059型は332個の箱に集中し、
40,611型が左右とも末尾3桁の形状箱を使っていた。
そこで、比率だけでなく、形状の末尾を5桁に固定する設定も併せて試した。
これは未解決型の分布の観測であり、内点存在の数値的な再確認ではない。

## 2. 小箱の端点は厳密に定義する

元の比率の箱を `H_b=[β^(b+1),β^b]` とする。
深さ `ℓ`、番号 `k` の箱は

\[
H_{b,\ell,k}=\left[
\beta^{b+1}+\frac{k}{2^\ell}(\beta^b-\beta^{b+1}),\quad
\beta^{b+1}+\frac{k+1}{2^\ell}(\beta^b-\beta^{b+1})
\right],\qquad 0\le k<2^\ell.
\]

証明書には元の `ratio_bin=b` と `ratio_refinement=[ℓ,k]` を保存する。
浮動小数点の端点を証明書の定義として使わない。
`β` は有理数なので、この追加によって厳密演算の体を広げる必要もない。

[ratio_refinement.hpp](ratio_refinement.hpp) は探索用の小箱を必要時に作る。
[verify_scalar_graph.py](verify_scalar_graph.py) は上式を有理数で再構成する。
従来の証明書は `ℓ=k=0` として扱い、従来の数学的ハッシュは変えない。
新しい属性を持つ証明書では、その属性もハッシュに含まれる。

## 3. 到着範囲と区間の直積を検証する

一つの後続には、次の条件を課す。

\[
H'\times J\subseteq\bigcup_i(H_i\times J_i).
\]

比率の射影と区間の射影がそれぞれ覆われるだけでは不十分である。
例えば比率の下半分では `J` の左側だけ、上半分では右側だけを持つと、直積に穴が残る。

探索では、既存の小箱の端点で `H'` を分割し、各帯で使える区間の合併を作る。
全ての帯で共通に覆える区間を後続の候補とし、実際に必要な子を帯ごとに選ぶ。
独立検証器は、有理数の全境界で同じ直積被覆を厳密に検証する。
左右交換、偶奇、形状変数の像の包含、親区間全体の被覆も引き続き検証する。

**箱を二分するだけの辺を、帰納の一段として追加してはいない。**
全ての帰納辺は、左右の少なくとも一方に合法な数字を追加する後続を伴う。
有限個の小箱の比率には正の下界があり、従来の収縮の論証を維持できる。
したがって、全依存先が閉じて厳密検証を通れば、
[有限証明書の十分条件](AUTOMATED_CLOSURE.md)によって初期区間の包含が従う。

## 4. 細分の順序と計算量を調整する

初期実装では、粗い箱で失敗したときだけ細分した。
これでは、粗い箱にいったん規則を付けて、その先で多数の義務を増やしやすかった。
次の版では、到着範囲が箱の片側だけに入る場合、まずその半分で受ける方法を試す。
この方法が作れなければ粗い箱に戻る。

試した末尾5桁固定の設定では、保存グラフ28,803型のうち15,396型が小箱を使い、
そのうち4,038型に局所規則が付いた。これら全てを厳密検証したという意味ではない。

候補の見積もりを記憶する方法も実装したが、実測の再利用率は初期比較で約2%にとどまった。
最終の追加実行ではこの記憶を無効にし、別の早期除外を使った。
親の担当区間が、ある後続の和の凸包から外れるパラメータ点を持つ場合、
その後続で当該区間全体を覆う候補を早めに捨てる。
子の比率の細分や辞書の照会に入る前に判定し、凸包は箱・後続ごとに再利用する。
最後の2実行では、それぞれ候補照会の81.17%・82.84%をこの段階で除外した。
これは照会数の割合であり、実行時間を同じ割合だけ短縮したという測定ではない。

この除外は浮動小数点による探索用の選別である。
成功の受理には使わず、候補が閉じた場合は全規則を独立に厳密検証する。
選別の変更で証明の候補を見落とす可能性はあり、探索の完全性や成功するまでの時間は保証しない。

## 5. 保存した厳密検証

- [ratio_first_examples.json](ratio_first_examples.json)：初期の細分から得た7局所規則。
  未解決158型を残した。[検証記録](ratio_first_examples.audit.json)。
- [ratio_clip_examples.json](ratio_clip_examples.json)：細分した親の規則と、細分した子を使う規則の計64個。
  未解決292型を残した。[検証記録](ratio_clip_examples.audit.json)。
- [ratio_filtered_frontier.json](ratio_filtered_frontier.json)：最後の10分実行から、初期型につながる64局所規則。
  全依存先と未解決305型を残した。[検証記録](ratio_filtered_frontier.audit.json)。

上記135規則は全て厳密検証を通過した。
最初の二つは局所例を集めたファイルなので、初期型からつながらない例も含む。
省略した規則の子を解決済みにはせず、全依存先を明示したまま未解決として残した。
これらの局所例だけで内点存在を証明したとはしていない。

テストでは、小箱の厳密な分割、必要な両半分の保持、不要な半分を要求しないこと、
片側を欠いた被覆の拒否、直積の穴の拒否、細分属性の検証とハッシュへの包含を確認した。
細分した箱を含むグラフの読み込みと、細分を捨ててしまう設定の拒否も検査した。
最終版で関連61テストが通過した（[実行ログ](ratio_tests.log)）。

## 6. 実行と継続

最後の二設定はそれぞれ600秒実行した。

| 設定 | 登録型 | 最終保存グラフの型 | うち細分した型 | 未解決 |
|---|---:|---:|---:|---:|
| 前回のグラフを継続・末尾3〜5桁 | 123,859 | 101,099 | 26,061 | 78,658 |
| 末尾5桁固定・新規探索 | 68,773 | 45,249 | 22,642 | 32,329 |

最終保存グラフについて、未解決型へ依存する規則を逆向きに除去し、
残る閉じた部分グラフが空であることも別途確認した。
現在選択されている規則の結果であり、別の規則や追加した型による閉包は排除しない。
未解決型数は、同じ証明の完成度が単調に変化する指標ではない。

[ratio_continued_state.json.gz](ratio_continued_state.json.gz) と
[ratio_fine_state.json.gz](ratio_fine_state.json.gz) に、両方の最終グラフを保存した。
これらの全局所規則を厳密検証したという意味ではない。
前回の保存状態も上書きせず残している。

```sh
# 保存済みの53,954型から、二分・四分の探索を行う。
python3 Berstein/kf131/lazy_type_search.py --method feedback \
  --plan Berstein/kf131/ratio_search_plan.json \
  --jobs 2 --output-dir /tmp/kf131-ratio-new

# 八分までの細分、到着範囲の先行切り詰め、形状箱の変更。
python3 Berstein/kf131/lazy_type_search.py --method feedback \
  --plan Berstein/kf131/ratio_clip_plan.json \
  --jobs 2 --output-dir /tmp/kf131-ratio-clip-new

# 後続の凸包による早期除外。各設定10分。
python3 Berstein/kf131/lazy_type_search.py --method feedback \
  --plan Berstein/kf131/ratio_filtered_plan.json \
  --jobs 2 --output-dir /tmp/kf131-ratio-filtered-new

# 今回保存した二つのグラフから、それぞれ探索を続ける。
python3 Berstein/kf131/lazy_type_search.py --method feedback \
  --plan Berstein/kf131/ratio_resume_plan.json \
  --jobs 2 --output-dir /tmp/kf131-ratio-resumed-new

python3 Berstein/kf131/verify_scalar_graph.py \
  Berstein/kf131/ratio_clip_examples.json --audit

cd Berstein/kf131
python3 -m unittest test_anchored_geometry test_type_graph \
  test_repair_search test_scalar_geometry test_scalar_search \
  test_lazy_search test_atlas_search test_block_search test_feedback_search \
  test_ratio_refinement -v
```

新しいグラフも `resume_graph` から継続できる。読み込み時の `ratio_depth` は、
保存グラフにある最大の細分深さ以上にする必要がある。
到達グラフの継続であり、現在の初期型から外れた辞書や失敗履歴まで復元するものではない。
