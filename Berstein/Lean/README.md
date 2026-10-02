# Hall’s ray の外にも Markov スペクトルの内点が存在する

**Lean による健全性証明と全表検査。**

Markov スペクトル \(M\) は、Hall’s ray \([c_F,\infty)\) より下にも
幅の正の区間を含みます。具体的に、次の包含を検証しました。

\[
[4.52578,4.52754]\subset M\cap(-\infty,c_F),\qquad
c_F=\frac{2221564096+283748\sqrt{462}}{491993569}
\]

したがって、実数直線の通常の位相で

\[
(4.52578,4.52754)\subset
\operatorname{int}\!\left(M\setminus[c_F,\infty)\right).
\]

**特に、\(4.52666\) は Hall’s ray の外にある \(M\) の内点です。**
得られた区間の幅は \(0.00176=11/6250\) です。

検証器の受理からこの内点の存在までを Lean で証明し、
元の表の **3,464,816行すべて**をその検証器のコンパイル実行で受理しました。
最終ビルド・公理監査・全表検査・6種の破損検査はすべて成功しました。
今回の保存記録は [verification-baseline.json](verification-baseline.json)、
再実行時の最新記録は `logs/verification.json` です。

## 検証方式

構成には、31313 を避ける尾と固定語 `(322,431)`、中心数字 4 を使います。
固定語 `431` に含まれる 4 は許し、追加する尾の数字を 1,2,3 に制限します。
131 禁止集合の内点構成という別の問題は対象に含めません。

大規模表には、**Lean で健全性を証明した検証器をコンパイル実行する**方式を使います。
`Main.lean` の主定理 `Berstein.target_interval_subset` の唯一の前提は
`Certificate.check input data alive cells = true` です。
和の充填、非中心値の上界、端点の意味、後続被覆を数学的な仮定として残す構成ではありません。

```lean
theorem target_interval_subset
    (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (h : Certificate.check input data alive cells = true) :
    Set.Icc targetLower targetUpper ⊆ markovSpectrum ∩ Set.Iio freimanConstant
```

同じ受理条件から `open_interval_subset_interior` と
`interior_below_freiman_nonempty` を導きます。
明示した内点は、区間の中点 `226333/50000 = 4.52666` です。

**約346万行の受理そのものを Lean カーネル内で還元した、前提のない閉じた定理ではありません。**
検証器の健全性はカーネルが検査し、具体的な表の受理はコンパイル実行で確認します。
この最後の実行には Lean のコンパイラ・実行系とファイルの読み込みを信頼します。
外部プログラムの成功フラグを公理として取り込むことはしません。

## 再現

Lean **4.32.1** と Mathlib **v4.32.1** を固定しています。
初めて依存関係を取得する場合は次を実行します。

```sh
cd Berstein/Lean
lake update
lake exe cache get
```

証明書の生成から、ビルド・公理監査・全表検査・破損入力の拒否確認まで実行するには：

```sh
python3 scripts/verify.py --prepare
```

生成済みの証明書を使って全表を再検査するには：

```sh
python3 scripts/verify.py
```

既に成功した全表実行を、実行ファイル・元入力・採用ビット列・全484証明書・ログの
ハッシュ照合を条件として再利用し、数学的証明と破損検査を再確認するには：

```sh
python3 scripts/verify.py --reuse-replay
```

全表の実行は既定で4分割並列です。この環境で最終実行の各分割は約12分でした。
証明だけをビルドする場合は `lake build`、公理を表示する場合は
`lake env lean Audit.lean` を使います。`lake build` 単独は全表の再検査を意味しません。
隣の `hall-ray` フォルダーへの実行時依存はありません。

## 証明の接続

| 段階 | 主なファイルと役割 |
|---|---|
| 実数の意味 | `Markov`, `Forbidden31313`, `CFInvariant`：両側無限連分数、禁止語の5状態オートマトン、無限尾の厳密な上下界 |
| 入力の検査 | `Quadratic462`, `QuadraticCF`, `SemanticCheck`, `SemanticSound`：二次体の演算、端点IDの厳密な等式、語・状態・偶奇・定数タグの検査 |
| 箱全体の保証 | `Normalization`, `FractionalLinear`, `SemanticTransport`, `GraphNumericSound`：連分数の正規化差、形状比、微分倍率の実数区間全体での保証 |
| 有限表の被覆 | `GraphCertificate`, `GraphCertificateFacts`：有理演算による比較、区間の連鎖、全採用行と全移動先、比の箱の被覆 |
| 無限列への接続 | `ActualCylinders`, `CylinderCover`, `GraphState`, `GraphSuccessor`：実際の接頭語、非空コンパクト円筒、入れ子性、両側の縮小、被覆点の実現 |
| 初期区間 | `RootFacts`, `RootCheck`, `RootState`：固定語322・431の端点和と比、初期25帯から所望の充填区間への接続 |
| 中心の支配 | `SpectralVerified`：すべての合法な尾と全非中心位置について `localValue ≤ 4525423/1000000`。4,372件の有限検査を `decide +kernel` で証明 |
| 主結果 | `CertificateCheck`, `Verified`, `Main`：有限検査の受理だけから区間のスペクトル所属と内点の存在を導く |

非中心値の評価は、近傍の有限検査と、遠方の内向き6桁・外向きオートマトン上界を使います。
元資料の遠方置換の議論を未証明のまま引用する構成にはしていません。

定数タグの一致は近似区間の重なりでは代用せず、二次体内の厳密な恒等式を検査します。
比の境界では検証済みの箱を選べることを証明し、境界に接する全ての箱が採用されているとは仮定しません。
有限グラフの閉性だけで充填を結論せず、連分数の円筒が実際に縮むことまで証明します。

## 元データと実行記録

元の `Freiman/data/graph_wide.dat` と `graph_wide.json.alive.bin` を直接読みます。
検証できない行を削除した表への置き換えは行いません。

| 項目 | 件数 |
|---|---:|
| 側の状態 | 22 |
| 状態の組 | 484 |
| 採用セル | 150,040 |
| 採用行 | 3,464,816 |
| 選択した子頂点 | 799,932 |
| 被覆経路の頂点総数 | 6,541,897 |

初期行は状態の組193、比の箱135、帯3〜27の25本です。
保存グラフのヘッダにある別の根番号を、今回の初期行の代用にはしません。

- `scripts/export_graph.cpp`：探索結果から有限の被覆証拠を生成する、信頼不要のプログラム。
- `scripts/export_semantics.py`：厳密な端点ラベル等を `Berstein/Data/Meaning.lean` に書き出す、信頼不要の生成器。
- `graphReplay`：入力の意味・根・準備した区間演算・全幾何の被覆を検査する Lean 実行ファイル。
- `generated/replay_report.json`：全分割の終了コード、範囲、件数、入力・実行ファイル・証明書・ログのハッシュ。
- `logs/verification.json`：最終定理の公理、Lean ソースのハッシュ、全表実行、破損検査をまとめた記録。

`NegativeControls.lean` は元ファイルを変更せず、6種の破損をメモリ上で作って拒否を確認します。
根の採用ビット、端点の厳密値、使われる定数、セル、採用行の被覆経路、選択した移動先マスクを対象とします。

## 証明と実行の信頼範囲

主要定理の依存公理を `Audit.lean` で列挙し、通常の Lean/Mathlib の
`propext`、`Classical.choice`、`Quot.sound` 以外が現れたら検証スクリプトを失敗させます。
`native_decide`、`sorry`、`admit`、新たな数学的公理は使用しません。
ハッシュは入力と実行の同一性を記録するもので、数学的な健全性の代用ではありません。

`markovSpectrum` は正整数の両側無限連分数と局所値の上限で定義します。
除外する半直線は明示的に `Set.Ici freimanConstant` です。
二次形式による別定義との同値性や、既知の Freiman 定数が半直線の最小端点であること自体は、
この区間包含の形式化とは別の定理です。

`HallRay/Basic.lean` と `HallRay/ContinuedFraction/{Basic,Mobius}.lean` は
[hall-ray](https://github.com/K-Yamada-2002/hall-ray) のコミット
`a584e5620124d23c709e3bbdc66db8b8b0586310` から複製しました。
MIT ライセンスは `HallRay/LICENSE`、元資料と複製ソースの SHA-256 は `sources.json` にあります。
