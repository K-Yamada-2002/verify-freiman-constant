# Freiman の半直線

このディレクトリには、禁制語31313を用いる後続被覆による
**$[c_F,\infty)\subset M\cap L$** の実装と固定証明書を置く。
数学的な証明はルートの [doc/](../doc/README.md) にある。
$c_F=(2221564096+283748\sqrt{462})/491993569$。
下端の最適性は対象外。

```sh
python3 -B -S Freiman/verify.py
```

Python 3.9以降の標準ライブラリと C++17 コンパイラを使う。
別の場所で実行する場合は、`Freiman/` とルートの `doc/` を同じ親の下へコピーする。
`Freiman/` 内で `python3 -B -S verify.py` と実行してもよい。
検証レポートには論文の TeX のハッシュも記録する。
`markov_interior/`、`Lean/`、`archive/` には依存しない。

## 構成

```text
Freiman/
├── verify.py          証明全体の実行入口
├── proof.py           局所条件・入口・非中心上界・半直線の接続
├── prepare.py         正確な連分数算術と入力生成
├── kernel.cpp         一般表の探索と固定表の全行検証
├── audit.py           独立した算術による入力の意味の検査
├── audit.cpp          別実装による全行検証（追加オプション）
├── README.md
├── TABLE_FORMAT.md    数値入力と採用表の形式
└── certificates/      必要な固定データ4ファイル
```

数学的な証明は [論文 PDF](../doc/out/lemma2_schecker.pdf)（[TeX](../doc/lemma2_schecker.tex)）を読み、
コードでは [verify.py](verify.py) から [proof.py](proof.py) をたどる。
[prepare.py](prepare.py) は算術と一般表の入力生成、[kernel.cpp](kernel.cpp) は重い有限計算を担当する。
[audit.py](audit.py) はこれらの算術や状態計算を import せずに検査する。

## 何を検証するか

既定の実行で、次を毎回再計算する。以前の成功フラグや保存済み検証結果の再利用は行わない。

- 数値入力とメタデータの再生成、一致の確認、独立した入力の意味の検査。
- 一般表の全3,464,816採用行の帰属と被覆。失敗行を削除して修復することはない。
- 端点付近の4局所条件と186後続、34件の初期入口と379後続。
- 93本の有限初期区間、43本の整数移動用区間。
- 91組の根と端点の根について、すべての非中心位置・無限延長に対する上界。
- $c_F$ での端点一致、$13/2$ までの接続、整数移動による無限大までの被覆、接合に使う余裕。

表から任意の実数を無限連分数として実現する極限の論証、中心値が最大値であること、
Lagrange スペクトルへの接合は論文の第2節・第4節・第6節にある。
コードとの対応は論文末尾の付録Aと、上の検証項目を参照。
この解析的な論証と有限検証を組み合わせた証明であり、半直線全体の Lean 形式証明ではない。

```sh
# 別実装でも全採用行を検査し、レポートを保存する。
python3 -B -S Freiman/verify.py --independent --output /tmp/freiman-proof.json

# 一般表だけを検査する。このモードは半直線包含を主張しない。
python3 -B -S Freiman/verify.py --table-only
```

ビルド生成物と中間結果は一時ディレクトリに置く。固定データは変更しない。
`--data` で入力ディレクトリを指定できる。`-O` は検証の assert を消すため受け付けない。

## 入力と探索

必要な固定データは [certificates/](certificates/README.md) の4ファイルだけ。
`.dat` は数値入力、`.meta.json` は状態・候補語などの意味、`.alive.bin` は採用する行、
`ray.json` は局所条件・入口・初期区間を指定する証明書である。
`.alive.bin` は1候補につき1バイトで、後続経路の記録ではない。
形式と添字は [TABLE_FORMAT.md](TABLE_FORMAT.md) を参照。

```sh
# 固定メタデータが指定する有限候補から、正確な数値入力を作る。
python3 -B -S Freiman/prepare.py --output /tmp/freiman-input
c++ -O3 -std=c++17 Freiman/kernel.cpp -o /tmp/freiman-kernel

# 採用表を与えると固定表の検証。
/tmp/freiman-kernel /tmp/freiman-input.dat /tmp/replay.json Freiman/certificates/graph_wide.alive.bin

# 採用表を省くと、全候補から被覆できない行を削除する探索。
/tmp/freiman-kernel /tmp/freiman-input.dat /tmp/search.json
```

探索が扱うのはメタデータに指定した有限状態・後続候補・比の箱・区間型の積である。
すべての連分数やすべての可能な証明を列挙しているわけではない。
探索結果は半直線全体の証明にならず、空になっても数学的な非存在は従わない。
元の `graph_wide` を発見した保護種付き拡張探索や、局所メニュー・初期根の探索は
[旧実装](../archive/2026-10-27/Freiman/README.md) に保存してある。
その発見履歴の再現と、固定証明書の再検証は区別する。

## 関連する証明

半直線より下の内点の証明は [markov_interior/](../markov_interior/README.md)、
共有する形式検証プロジェクトは [Lean/](../Lean/README.md) にある。
実験・過去の探索・旧文書・生成済みバイナリは [archive/](../archive/README.md) に保存した。
