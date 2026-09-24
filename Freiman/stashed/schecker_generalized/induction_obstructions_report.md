# 帰納法の障害の厳密な検出と、被覆規則の修正

続き: [子の区間型を追加する帰納探索](adaptive_induction_report.md)。以下の反例を探索へ組み込み、失敗した被覆から新しい端点型を生成している。

2026-09-22。**帰納法の閉鎖は未達成。** 今回は、以前の証明義務のうち7族がそのままでは成立しないことを証明し、それらを初期区間から到達しないように被覆規則を修正した。さらに、周期帰還で正確に保存されるパラメータを得た。

修正後の監査では、到達可能な局所規則は18族、未証明の末端は32族。既知の7反例を含む義務への到達はなくなった。32族の充填、およびその後の閉鎖は未証明である。

## 1. 未証明だった区間の一部は実際に埋まらない

記号は [子の被覆の報告](child_induction_report.md) と同じ。以下はすべて `n=0`、中心の4を加える前の値である。各行の開区間は、その接頭語からの**どんな合法な無限継続の和にも属さない**。

| 要求されていた区間 | 左右それぞれの分割深さ | 隙間の下端（概数） | 隙間の上端（概数） |
|---|---:|---:|---:|
| `J1R_(11,13)` | 5 | 0.527931708194161 | 0.527931708300240 |
| `H_(111,1)` | 5 | 0.527930757233207 | 0.527930758757887 |
| `J4R_(112,31)` | 5 | 0.527867670280455 | 0.527867670398683 |
| `J1_(122,3)` | 5 | 0.527848209092551 | 0.527848209154096 |
| `J1R_(31,1112)` | 5 | 0.527984789682140 | 0.527984789719998 |
| `H_(33,12)` | 5 | 0.527986625448117 | 0.527986634466988 |
| `J3_(3,111)` | 6 | 0.527987050444337 | 0.527987050562687 |

最初の6行は前回の36末端の調査から得た。最後の行は、その手前の局所規則の親自体を調べて得た。`n=0` の一例で、全 `n≥0` の充填義務を反証できる。

**以前の局所被覆の等式・包含が誤りだったわけではない。** 子の区間の合併が親を覆うことと、その子の区間内のすべての点が実現できることは別である。今回の反例は、後者をそのまま帰納命題にすることを排除する。

`induction_obstructions.json` は端点を `Q(√462)` の有理係数で記録する。`frontier_obstructions.py --verify` は浮動小数点探索を呼ばず、以下を確認する。

1. 保存した隙間が、要求した型の区間内にある。
2. 左右それぞれの合法な深さ `d` の円柱をすべて列挙する。
3. すべての円柱凸包の和が、その開区間を避ける。

最後の確認は、左右の円柱を順に並べ、上端の和が隙間以下なら左の添字を増やし、下端の和が隙間以上なら右の添字を減らす方法で行う。それぞれ、未処理の長方形の1行または1列を厳密に排除する。どちらでもなければ検証を拒否する。これにより無限継続をすべて排除できる。

## 2. 反例を通る分岐を修正した

以前から探索に用意されていた8形状のうち、追加の4形状は次のもの。

| 型 | 一方の端点 | 他方の端点 |
|---|---|---|
| `J5` | `L₁⁻+R₃⁺` | `L₂⁺+R₂⁻` |
| `J6` | `L₁⁻+R₂⁻` | `L₂⁺+R₃⁺` |
| `J7` | `L₁⁻+R₁⁺` | `L₂⁺+R₃⁺` |
| `J8` | `L₁⁻+R₁⁻` | `L₁⁺+R₂⁺` |

小さい方を下端とする。`R` は左右交換。±は変換前の合法な末尾の極値であり、変換後の大小ではない。

次の6規則を、**すべての `n≥0`** について厳密に証明した。

\[
\begin{aligned}
H_{11,1}&\subset J^{5R}_{11,13}\cup H_{11,12}\cup J^{1R}_{111,1},\\
H_{11,3}&\subset H_{113,3}\cup J^{5R}_{11,31}\cup H_{111,3},\\
H_{12,3}&\subset J^1_{123,3}\cup J^{5R}_{12,32}\cup H_{121,3},\\
H_{3,12}&\subset J^5_{33,12}\cup H_{32,12}\cup H_{31,12},\\
J^{2R}_{3,1}&\subset J^{7R}_{3,11}\cup J^{8R}_{31,1}\cup H_{3,12},\\
J^{1R}_{3,11}&\subset J^{6R}_{3,112}\cup J^{6R}_{32,112}\cup J^{3R}_{31,11}.
\end{aligned}
\]

例えば `H_(33,12)` 全体を要求する代わりに `J5_(33,12)` を使う。初期からの到達可能性を数え直すと、反証された7族はすべて消える。最後の規則の親 `J1R_(3,11)` 自体も、新しい初期からの経路では到達しなくなる。

証明書は `gap_repaired_covers.json`。`n=0` を直接、`n≥1` を `x∈[0,1/85]` の箱で処理する既存の厳密検証器により、合法性、端点の順序、接触、親全体の被覆を再検証した。子の総追加長は2以下。

探索時には既知の厳密な反例と `n=0` の両側5桁の隙間を持つ候補を除外した。**この除外を通過しても、子の内部の充填は証明されない。** 検証済み規則は置換後も20族あり、そのうち初期から到達するものが18族。`gap_repaired_audit.json` に32末端を明記した。

## 3. 周期帰還で保存されるパラメータ

\[
M(U)=\begin{pmatrix}a_U&b_U\\c_U&d_U\end{pmatrix},\quad
r=c_U/d_U,\quad s=c_V/d_V,\quad q=d_U^2/d_V^2
\]

とし、左右の極値末尾を `α,β` とする。次の比を使う。

\[
R_{\alpha,\beta}
=q\frac{(1+r\alpha)^2}{(1+s\beta)^2}
=\frac{|T_V'(\beta)|}{|T_U'(\alpha)|}
=\left(\frac{c_U\alpha+d_U}{c_V\beta+d_V}\right)^2.
\]

`α=T_u(α')`, `β=T_v(β')` のとき、行列の積から

\[
R' = R\left(\frac{c_u\alpha'+d_u}{c_v\beta'+d_v}\right)^2
\]

となる。`31313` 回避の極値には、前周期のない6つの周期位相がある。それぞれの周期語 `w` と値 `z` に対して

\[
M(w)\binom z1=(43+2\sqrt{462})\binom z1
\]

が厳密に成立する。従って、左右をそれぞれ対応する周期語で延長すれば **`R'=R`**。これは箱の誤差を毎回加算しない帰還条件である。

初期族では

\[
\alpha=\zeta=\frac{2\sqrt{462}-28}{19},\qquad
\beta=\xi=\frac{2\sqrt{462}-29}{53}
\]

を選べば、帰還語は `131213` と `313121`。すべての `n≥0` で

\[
R_{\zeta,\xi}(U_n,V_n)
=\frac{2941188465121+134881150564\sqrt{462}}{6906504888529}
\approx0.845630170066686.
\]

`periodic_anchor_invariant.py` は共通固有値の恒等式を厳密に検証する。有限個の `n` を試すことで全指数に拡張しているのではない。この結果は**周期経路のパラメータ更新**を閉じるが、そこから分かれる区間の被覆までは証明しない。

## 4. 閉じた区間系の探索結果

端点形状を固定せず、合法な1桁追加の両側端点の組をすべて候補にし、子へ継承できる区間成分を繰り返し残す探索も行った。

| パラメータ | 箱の数 | 後続 | 結果 |
|---|---:|---|---|
| 従来の `q` | 1,800 | 総追加長2以下 | 14回の更新で空の固定点 |
| 極値末尾での微分比 `R` | 3,600 | 総追加長2以下と左右6桁ずつの極値後続 | 24回の更新で空の固定点 |

それぞれ `invariant_endpoint_components.py`、`invariant_anchor_components.py` と対応する `_float.json` に保存した。箱の基底は0.88、25分割、末尾状態は6種類。微分比の探索では親と子で極値末尾の選択を変えることも許した。

これらは浮動小数点による十分条件の探索であり、貪欲な区間の合併、端点候補への丸め、パラメータの外側評価を含む。空になったことから、有限帰納系の不可能性は結論できない。

初期の3区間は `n=0` で両側7桁まで、初期全凸包 `A_0,A_1` は両側8桁まで、浮動小数点探索で隙間を検出しなかった。`initial_gap_checks.json` に保存した。これも充填の証明ではない。

残る課題は、周期帰還の外側にある区間を、子へ継承できる領域へ割り当てること。今回の不変量で得た `q` と `r,s` の関係を保つ領域、または目標値と選択履歴を含む領域が必要になる可能性がある。単に現在の32族を充填済みと仮定して閉鎖を宣言することはできない。

## 再実行

追加後の全28テストが通過した。保存済みの反例と被覆の厳密リプレイ、実現可能な境界点を誤って隙間に含めた証明書の拒否、旧監査で7反例が検出され修正後には到達しないこと、周期固有値の恒等式を確認する。無限の区間充填を証明するテストではない。

```sh
python3 Freiman/schecker_generalized/frontier_obstructions.py --verify Freiman/schecker_generalized/induction_obstructions.json
python3 Freiman/schecker_generalized/child_family_covers.py --verify Freiman/schecker_generalized/gap_repaired_covers.json
python3 Freiman/schecker_generalized/periodic_anchor_invariant.py
python3 Freiman/schecker_generalized/repair_child_covers.py --output /tmp/gap_repaired_covers.json
python3 Freiman/schecker_generalized/audit_child_covers.py \
  Freiman/schecker_generalized/child_family_covers.json \
  Freiman/schecker_generalized/child_family_covers_deep.json \
  Freiman/schecker_generalized/child_J1_covers.json \
  Freiman/schecker_generalized/child_J2R_covers.json \
  Freiman/schecker_generalized/child_H11_1_cover.json \
  Freiman/schecker_generalized/child_frontier_covers.json \
  Freiman/schecker_generalized/gap_repaired_covers.json \
  --obstructions Freiman/schecker_generalized/induction_obstructions.json
python3 -m unittest discover -s Freiman/schecker_generalized -v
```
