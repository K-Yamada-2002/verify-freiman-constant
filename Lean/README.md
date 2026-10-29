# Shared formal verification

This is the repository-wide Lean project. It hosts common definitions and
lemmas alongside concrete verification targets; it is not restricted to the
interior-interval construction.

| Library | Current contents |
|---|---|
| `SpectrumVerification` | Project-wide entry point importing the available libraries |
| `HallRay` | Definitions and continued-fraction lemmas shared with the original Hall-ray project |
| `Berstein` | The existing checker-soundness proof and original Markov interior-interval construction |
| `Freiman` | Checker soundness for the complete half-line `[c_F,∞) ⊆ M`; [verification guide](Freiman/README.md) |

The `Berstein` namespace is retained to preserve existing theorem names and
imports. The computational project is now [Markov_interior/](../Markov_interior/README.md).
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

The [Freiman verification](Freiman/README.md) now connects the exact endpoint
`c_F`, all four local successor systems, the finite chain, and the upper ray:

```sh
python3 -B scripts/verify_freiman.py --reuse-replay
```

`Freiman.ray_subset_markov_of_check` is the kernel-checked soundness theorem;
the pipeline establishes concrete finite acceptance by Lean checker execution.
The extended `31313,13131` table and its extended interior endpoints remain
outside these verification targets. The Freiman result here concerns the Markov
spectrum; Lagrange-spectrum inclusion and optimality below `c_F` are not claimed.

## Data and provenance

The concrete Lean checker reads `../Freiman/certificates/graph_wide.dat` and its
adoption array. `scripts/input_semantics.py` contains the independent exact
arithmetic, input audit, root checks, and three corruption controls used by the
untrusted semantic-label exporter. Run it separately with:

```sh
python3 -B scripts/input_semantics.py
python3 -B scripts/export_semantics.py
```

The exporter regenerates `Berstein/Data/Meaning.lean`; the mathematical labels
must still pass Lean's checker. The relocation preserves the generated labels.

`sources.json` checks the current table, metadata, adoption array, and relocated
input-audit module using repository-relative paths. Vendored Hall-ray hashes
remain relative to this project. Historical source hashes and their origin are
recorded under `historical_provenance`, pinned to Git commit
`2ac2b5e20dedd8255954c5a32f5694649defd771`. They document provenance and are not
read during verification. Previous implementations and audit records can be
retrieved from that commit; no historical directory is needed at runtime.
