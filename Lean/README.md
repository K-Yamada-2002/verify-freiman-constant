# Shared formal verification

This is the repository-wide Lean project. It hosts common definitions and
lemmas alongside concrete verification targets; it is not restricted to the
interior-interval construction.

| Library | Current contents |
|---|---|
| `SpectrumVerification` | Project-wide entry point importing the available libraries |
| `HallRay` | Definitions and continued-fraction lemmas shared with the original Hall-ray project |
| `Berstein` | The existing checker-soundness proof and original Markov interior-interval construction |

The `Berstein` namespace is retained to preserve existing theorem names and
imports. The computational project is now [markov_interior/](../markov_interior/README.md).
New results can add their own libraries to `lakefile.toml` and imports to
`SpectrumVerification.lean`; reusable lemmas can be shared across those targets.
No new verification target is claimed merely from reorganizing these files.

## Build the available proofs

Lean and Mathlib are pinned to **4.32.1**. From the repository root:

```sh
cd Lean
lake update
lake exe cache get
lake build
```

The dependency setup is needed for a fresh checkout. `lake build` builds the
project-wide library. Use `lake build HallRay` or `lake build Berstein` for a
specific library. This checks the theorem sources; it does not replay every
row of a concrete large certificate.

## Verify the original interior-interval certificate

The current execution pipeline still concerns the original `31313` table and
interval `[4.52578,4.52754]`. From `Lean/`:

```sh
python3 -B scripts/verify.py --prepare
```

It builds the proved-sound checker, audits theorem axioms, replays the entire
3,464,816-row table, and runs corruption controls. With prepared witness files,
omit `--prepare`. `--reuse-replay` reuses execution evidence only after checking
the executable, input, adoption array, witnesses, and logs.

Read the [result-specific guide](Berstein/README.md) for theorem statements,
module responsibilities, reproduction steps, and the execution trust boundary.
The large-table acceptance is established by compiled checker execution;
the soundness implication is kernel-checked. The original
[verification baseline](verification-baseline.json) remains a historical record.

The extended `31313,13131` table, its extended interval endpoints, and the whole
Freiman-ray construction have not been formalized here. Their Python/C++
verification must not be presented as additional Lean theorems.

## Data and provenance

The concrete Lean checker reads `../Freiman/certificates/graph_wide.dat` and its adopted
array. The provenance records in `sources.json` refer to the original source
snapshot under `../archive/2026-10-26/`; the verification script resolves those
historical paths there. Vendored Hall-ray source hashes remain relative to this
project. The theorem sources, pinned dependency revisions, and saved table bytes
were preserved when this project moved to the repository root.
