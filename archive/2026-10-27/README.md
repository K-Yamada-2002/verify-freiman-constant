# 単純化前の Freiman ツリー

[Freiman/](Freiman/README.md) は、`verify/search/common/history` に分けていたツリーを
ファイルごと移した保存物である。全データ・過去の探索・実験・旧論文・ログ・生成済み実行ファイルを残した。
このツリー自身の README は移動前の説明を保存している。

現在の入口は [Freiman/verify.py](../../Freiman/verify.py)、
証明と実行の説明は [現在の README](../../Freiman/README.md)。
一般表、メタデータ、採用配列、統一した半直線証明書は、現在の `certificates/` にも同じバイトで保存した。
新しいコードはこの保存物に依存しない。

## 過去の探索と証明を再実行する場合

当時のモジュール名 `Freiman.*` を維持するため、この `Freiman/` を別の作業ディレクトリへコピーし、
その親からモジュールとして実行する。例えばリポジトリの根から：

```sh
work=$(mktemp -d /tmp/freiman-history.XXXXXX)
cp -R archive/2026-10-27/Freiman "$work/Freiman"
cd "$work"
python3 -B -S -m Freiman.verify.verify_unified_proof --full
```

コピーした保存物には現在の6ファイル構成とは別の `data/`、`logs/`、`bin/` があり、
当時の実行はそこへ結果を書き出す。探索によっては NumPy を追加で必要とする。
バイナリは過去の生成物なので、使う環境でソースから再コンパイルする。
保護種付き表拡張は `search/graph_kernel_expand.cpp`、局所メニューと初期根の探索は
`search/endpoint_return.py`、`adaptive_return_chart.py`、`wide_bootstrap_search.py` などにある。
固定表を独立に再検証しなければ、種を保護した探索の成功は閉包証明にならない。

`FREIMAN_PROOF_SUMMARY.md` は単純化時に作った証明要約の保存物。
現在は論文と説明が重複するため、現行ツリーから外した。現行の証明・実行には用いない。
