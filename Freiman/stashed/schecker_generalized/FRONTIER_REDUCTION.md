# 未解決の帰納義務を減らす被覆の選び直し

2026-09-23。対象は引き続き

\[
P=313121,\qquad A_n=(3211P^n3\mid4322P^n),\qquad n\ge0
\]

の**凸包全体**。新たな数字は `{1,2,3}`、禁止語は `31313`。
初期目標を狭めず、端点テンプレート48種類を保持して探索を整理した。
**全帰納は未完成。局所規則の検証と、無限の充填の証明は区別する。**

最新の保存状態は到達ケース2,848、局所規則1,064、未解決1,784。
前回の未解決3,512件から1,728件、約49.2%減らした。
全局所規則の厳密監査は失敗0件で、探索状態の復元一致も確認済み。
選択済み規則で閉じた部分系は0件、全帰納の検査は節点2255の未解決義務で拒否された。

## 1. 改良の狙い

前回の部分戦略には、領域が狭くなって必要性を失った子も残っていた。
また、同じ未解決義務へ到達する子を別々に数えると、被覆の選択を誤りやすい。
そこで型を追加する前に、次の処理を行う。

1. 全入辺から必要なパラメータ範囲を集め、相関を保持して領域を縮小する。
2. 元の被覆から、目標全体を覆う部分列を選び直す。
3. 他の到着先で全像を受け持てる場合、冗長な到着先の参照を削る。
4. 到達不能になった義務を除く。
5. 既存の被覆手順を未解決型の領域で再検証し、成立すれば局所規則として採用する。

前半は [reduce_chart_frontier.py](reduce_chart_frontier.py)、後半は
[reuse_chart_rules.py](reuse_chart_rules.py) に実装した。

## 2. 子の先にある未解決義務を数える

未解決節点 \(i\) には集合 \(F(i)=\{i\}\) を置く。
局所規則を持つ節点では、子の集合の和を逆向きに伝播する。
有限グラフの最小不動点を計算するため、帰還を含めても
\(F(i)\) は「選択済みの規則から到達する未解決節点全体」と一致する。

被覆鎖 \(C\) の主な評価値を

\[
\left|\bigcup_{j\text{ is a destination of }C}F(j)\right|
\]

とする。同じ義務へ合流する複数の子は一度だけ数え、局所規則があるだけの子を
費用0とは扱わない。空集合になる局所型だけが、選択済み規則で閉じた部分系に属する。

元の被覆の順序を保った有向非巡回グラフ上で、接触と厳密な前進を満たす鎖を探す。
各終点に保持する候補は既定32個。候補の切り捨ては探索上の近似であり、
大域的最適性や、他の被覆の不存在を主張するものではない。
受理した鎖はすべて既存の厳密検証器へ戻す。

## 3. 縮小・削除が必要な部分を失わない理由

- 領域の縮小は、全入辺の像と初期族の像を**同時に**読んでから行う。
  周期の不動点への収束を仮定しない。
- 到着先を削る際には、残りの到着先が後続のパラメータ像全体を覆うことを
  `checker.child` で確認する。場合分けの一部分を勝手に捨てない。
- 被覆鎖から辺を削る際には、元の目標区間の両端と、全ての接触を厳密に確認する。
- 新しい直接依存先が一つも増えていないことも集合比較で確認する。
- 各反復の後に全局所規則と初期族を独立に再監査する。

したがって、削除された未解決義務は「充填できた義務」ではなく、
**残した帰納戦略では証明する必要がなくなった義務**である。
未解決数の削減率は証明の完成度を表さない。

## 4. 既存規則を別の型で使い直す

広い型への参照を追加するだけでは、今回の検証器が要求する
「到着先領域全体での区間包含」が成立しない場合がある。
そこで既存型の**実際の桁追加と被覆手順**を取り出し、
未解決型の元の領域・元の区間の上で最初から検証する。

この再利用では、状態・偶奇・向きが一致する通常規則を候補とする。
候補の順位付けに使う浮動小数の外側箱は証明の受理条件ではない。
接触、桁の合法性、到着先への包含、後続の全像被覆は全て
\(\mathbb Q(\sqrt{462})\) の厳密演算で確認する。

参照先は最初から到達していた型だけであり、新規の型も、桁を追加しない帰納辺も作らない。
成功した未解決節点には局所含意が付くが、その子の義務は引き続き残る。
場合分け付き規則の移植は、適用領域の変換が別途必要なので今回の候補生成には含めない。

`--optimize-local` は、すでに局所規則を持つ節点にも再利用を試す。
元のグラフから計算した未解決の依存先数が厳密に減る候補だけを再検証し、
成功時に置き換える。この評価値は一回の探索中は固定であり、最適性の保証はない。
置換後には到達グラフを作り直して実際の未解決数を測る。

## 5. 同じ出発点での比較

出発点は [前回の部分戦略](piecewise_incoming_selective.json)。
「領域縮小のみ」と「被覆も選び直す」の4回反復は、同じグラフ・同じ回数で比較した。

| 処理 | 到達ケース | 局所規則 | 未解決 |
|---|---:|---:|---:|
| 出発点 | 4,989 | 1,477 | 3,512 |
| 領域縮小のみ4回 | 3,948 | 1,243 | 2,705 |
| 領域縮小＋被覆の選び直し4回 | 3,268 | 1,022 | 2,246 |
| 上の4回の結果に規則再利用 | 3,268 | 1,187 | 2,081 |
| 領域縮小＋被覆の選び直し8回 | 2,984 | 968 | 2,016 |
| 上の8回の結果に規則再利用 | 2,984 | 1,106 | 1,878 |
| さらに縮小・被覆選び直しを3回 | 2,890 | 1,082 | 1,808 |
| さらに未解決型での再利用と局所規則の置換 | 2,851 | 1,067 | 1,784 |
| 同義の義務を統合して探索状態へ保存 | 2,848 | 1,064 | 1,784 |

4回同士の比較では、新方式は対照より未解決を459件減らした。
8回整理した後の規則再利用では、2,016件を走査し、10,894候補を試し、
138件に厳密な局所規則を付けた。4回の枝の165件とは別実験であり、合算しない。

続いて、8回の枝の再利用結果に縮小・整理を3回追加し、1,808件へ削減。
ここで全2,890ケースに既存手順を試し直し、23,782候補のうち、
未解決3件への規則追加と、局所規則13件の置換を受理した。
不要になった節点を除いた結果、未解決は1,784件になった。

別の比較枝として、1,878件の段階で直ちに局所規則も置き換える実験も行った。
こちらは新規局所規則1件、置換17件で、未解決1,854件。
この結果は上の11回整理した枝へ合算していない。

全行で厳密監査の失敗は0件、選択済み規則だけで閉じた部分系は0件。
局所規則数が途中で減るのは、到達不能になった規則も削除したためである。

- [4回の対照](frontier_contraction_control.json)・[監査](frontier_contraction_control.audit.json)
- [4回の新方式](frontier_reduced_four.json)・[監査](frontier_reduced_four.audit.json)
- [4回の枝での規則再利用](frontier_recipe_four.json)・[監査](frontier_recipe_four.audit.json)
- [8回の新方式](frontier_reduced_eight.json)・[監査](frontier_reduced_eight.audit.json)
- [8回の枝での規則再利用](frontier_recipe_eight.json)・[監査](frontier_recipe_eight.audit.json)
- [追加3回の整理](frontier_reduced_eleven.json)・[監査](frontier_reduced_eleven.audit.json)
- [整理後の規則追加・置換](frontier_final.json)・[監査](frontier_final.audit.json)
- [8回の枝で直接規則を置き換えた比較実験](frontier_policy_eight.json)・[監査](frontier_policy_eight.audit.json)

## 6. 検証

関連する28試験を実行して全件通過した。

```sh
cd Freiman/schecker_generalized
python3 -m unittest test_frontier_reduction test_rule_reuse \
  test_chart_contraction test_piecewise_charts test_reachable_charts
```

循環グラフの未解決依存先を別実装の探索と照合し、共有依存先の重複計数を確認した。
必要な接触を削る例、空の桁追加、場合分けを持つ規則の置換失敗も検査する。
厳密な受理処理は小数変換を禁止した状態でも試験し、失敗時の元の規則への復元を確認した。
未解決が残る実例に対して、全帰納の検査が拒否することも確認している。

再現例:

```sh
python3 reduce_chart_frontier.py piecewise_incoming_selective.json \
  --rounds 4 --output /tmp/frontier-four.json
python3 reduce_chart_frontier.py /tmp/frontier-four.json \
  --rounds 4 --output /tmp/frontier-eight.json
python3 reuse_chart_rules.py /tmp/frontier-eight.json \
  --seconds 240 --candidates 32 --output /tmp/frontier-reused.json
```

時間上限付きの探索は実行環境で試行数が変わりうる。
保存した証明書は、探索の候補選びに依存せず独立に監査できる。

## 7. 保存状態と続行

- [整理・統合後の部分戦略](frontier_compacted.json)
- [独立した厳密監査](frontier_compacted.audit.json)
- [続行用の完全探索状態](frontier_compacted.state.json)
- [保存・復元の一致確認](frontier_compacted.roundtrip.json)
- [機械可読な実験一覧](frontier_reduction_report.json)

全ての初期目標と桁追加の条件を保持している。
新しいケースを追加することなく、不要な義務の削除と既存規則の利用を進めた。
取り込み時には、パラメータ領域と厳密な両端点が一致する3ケースを統合した。
この統合でも未解決数は1,784のままである。

今回縮小した領域は前回の探索義務と意味が異なるため、旧領域上の探索失敗は引き継がない。
元の完全状態 `piecewise_incoming_selective.state.json` は別に保持した。
新状態は `piecewise_specialized_initial.state.json` の共通設定・48端点型を使い、
局所規則を取り込み前後で監査して作成した。義務処理回数は新状態では0から始まる。

同じ探索器で復元し、完全な状態、待ち行列の順序、設定、証明書ハッシュの一致を確認した。
永久棄却の集合のみ順序を正規化して比較した（新状態では空集合）。
証明書ハッシュ:

```text
27617115843acdc30f6c0f1e5d02d175c4d50fb5fb4ddc59298301b417089feb
```

追加整理・規則置換・探索状態への取り込みは次で再現できる。

```sh
python3 reduce_chart_frontier.py frontier_recipe_eight.json \
  --rounds 3 --output /tmp/frontier-eleven.json
python3 reuse_chart_rules.py /tmp/frontier-eleven.json \
  --seconds 180 --candidates 32 --optimize-local --output /tmp/frontier-final.json
python3 specialize_piecewise_search.py /tmp/frontier-final.json \
  --source-state piecewise_specialized_initial.state.json \
  --output /tmp/frontier-new.state.json
```

保存した最終状態から探索を続ける例:

```sh
python3 search_piecewise_charts.py frontier_compacted.state.json \
  --seconds 180 --max-steps 1000 --max-types 4000 \
  --output /tmp/frontier-continued.json
```

新しい探索では再び子の義務が増える場合があるため、被覆の選択・整理後の
到達する未解決数を測り、今回の保存状態と比較する。
残る1,784件は有限の候補探索で未解決という意味で、充填の不可能性を示した件数ではない。
