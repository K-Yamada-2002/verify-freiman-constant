# Verification

Start with **[graph_kernel.cpp](graph_kernel.cpp)**. This is the integer-interval
checker for the original table. It also supports deletion search; there is one
implementation for these two modes, rather than a copy in `search/`.

| Source | Role |
|---|---|
| [verify_unified_proof.py](verify_unified_proof.py) | Current whole-ray proof entry point |
| [verify_invariant_certificate.py](verify_invariant_certificate.py) | Exact input regeneration and fixed-table replay |
| [verify_closed_root.py](verify_closed_root.py) | Algebraic replay of an extracted root menu |
| [local_invariant_returns.py](local_invariant_returns.py) | Verification of current local return conditions |
| [verify_graph_controls.py](verify_graph_controls.py) | Positive and negative table-checker controls |
| [verify_dyadic.py](verify_dyadic.py), [check_dyadic.cpp](check_dyadic.cpp) | Cross-check integer rounding against rational arithmetic |

Run from the repository root:

```sh
python3 -B -S -m Freiman.verify.verify_unified_proof --full
```

For table closure alone:

```sh
python3 -B -S -m Freiman.verify.verify_invariant_certificate graph_wide
```

Python resolves the package-relative imports directly. See the [code guide](../../README.md#code-start-here),
[data format](../TABLE_FORMAT.md), and [project README](../README.md).
