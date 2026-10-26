# 論文

数学的な論文は、このディレクトリにまとめる。

| 論文 | TeX | PDF |
|---|---|---|
| Markov スペクトラムに含まれる区間について | [paper.tex](paper.tex) | [paper.pdf](paper.pdf) |
| Freiman 半直線の Schecker 型証明 | [lemma2_schecker.tex](lemma2_schecker.tex) | [lemma2_schecker.pdf](out/lemma2_schecker.pdf) |

`paper.tex` は後続被覆の共通原理、Freiman 半直線の検証、半直線以外の内点の構成を扱う。
`lemma2_schecker.tex` は Freiman 半直線の詳細な証明と、付録Aで実装との対応を説明する。
`out/` にはコンパイル出力を置く。

実装・証明書・実行方法は [Freiman/](../Freiman/README.md) と
[Markov_interior/](../Markov_interior/README.md)、形式検証は [Lean/](../Lean/README.md) を参照。
現在の拡張された内点区間の論証は [Markov_interior/PROOF.md](../Markov_interior/PROOF.md) にある。
