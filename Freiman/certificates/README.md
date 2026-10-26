# 固定証明書

証明に必要なデータは次の4ファイル。

| ファイル | 内容 |
|---|---|
| [graph_wide.dat](graph_wide.dat) | 厳密な外向き丸めによる数値入力 |
| [graph_wide.meta.json](graph_wide.meta.json) | 状態、語、後続候補、箱、区間型の定義 |
| [graph_wide.alive.bin](graph_wide.alive.bin) | 4,801,280候補中3,464,816行を採用する1バイト配列 |
| [ray.json](ray.json) | 4局所条件、34入口、有限部93本、整数移動用43本 |

いずれも旧 `data/` にあった固定入力とバイト単位で同じ。
採用配列の旧名は `graph_wide.json.alive.bin`、半直線証明書の旧名は
`unified_proof_certificate.json`。
メタデータに残る発見時のラベルや小数は、正確な受理判定の代わりには使わない。

`verify.py` は毎回入力を再生成し、表を検証してから半直線の有限条件を再計算する。
保存済みの検証レポートや探索時の成功フラグは入力として必要ない。
表の意味と採用添字は [TABLE_FORMAT.md](../TABLE_FORMAT.md)、
数学的な論証は [論文](../../doc/out/lemma2_schecker.pdf) を参照。
