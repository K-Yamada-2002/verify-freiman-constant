# Compatibility paths

The actual sources now live in [verify/](../verify/README.md),
[search/](../search/README.md), [common/](../common/README.md), and
[history/](../history/README.md). Files here are relative symbolic links that
preserve old commands, flat imports, and paths in verification records.

Source contents and fixed inputs are unchanged. Edit the actual files in the
role directories rather than creating a second copy here. Use root `run.py`
to execute Python sources at their new paths; see [CODE.md](../../CODE.md).
The separate `audit/` and `Lean/` directories retain their existing locations.
