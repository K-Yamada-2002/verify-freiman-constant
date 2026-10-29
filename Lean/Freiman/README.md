# Freiman half-line in the Markov spectrum

The target is `[c_F,∞) ⊆ M`, where `c_F` is the exact quadratic Freiman
constant. `Freiman.ray_subset_markov_of_check` proves this inclusion from a
single finite executable acceptance predicate, `Freiman.rayCheck`. It assumes
no interval filling, spectral domination, or Markov membership results.

The mathematical implication is checked by the Lean kernel. Acceptance of the
large concrete certificate is established by executing these proved-sound Lean
checkers, as in the original interior-interval verification. The large table is
not reduced inside the kernel. No `sorry`, `native_decide`, or extra mathematical
axioms are used; the axiom audit permits only `propext`, `Classical.choice`, and
`Quot.sound`.

## Proof components

| Modules | Content |
|---|---|
| `Setup`, `CylinderCover`, `GraphState`, `GraphSuccessor` | Actual compact continued-fraction cylinders and infinite realizations for arbitrary fixed root words, using the existing general table |
| `Root`, `RootCover` | Actual root-word checks, exact quadratic endpoints, finite sum coverage, and the upper ray `[13/2,∞) ⊆ M` |
| `Markov`, `Spectral`, `FiniteRay` | Central gluing, uniform noncentral bounds, and a finite chain from the initial interval to `13/2` |
| `Endpoint`, `LocalInvariant` | Exact endpoint `c_F`, periodic returns, recurrent shape boxes, and the `33` loop's invariant at `ζ=(√13−3)/2` |
| `Coordinate`, `LocalSide`, `LocalCheck`, `LocalSound`, `LocalGeneral`, `LocalSelf` | Sound local successor checks, actual word extensions, and interval conversion between the `S` and `V_ζ` coordinates |
| `LocalCover`, `Initial` | One combined local/general infinite construction, realizing the closed interval starting exactly at `c_F` |
| `Main` | Joins the initial interval, finite chain, and upper ray into `[c_F,∞) ⊆ M` |

This target does not include the Lagrange-spectrum inclusion or optimality
below `c_F`.

## Reproduce

From `Lean/`, with the existing general-table witness files:

```sh
python3 -B scripts/verify_freiman.py --reuse-replay
```

The original table verifier validates the hashes behind reused full-table
execution, builds the checker, audits its axioms, and reruns corruption
controls. Omit `--reuse-replay` to execute the entire table again. For a fresh
checkout, prepare witnesses first with `python3 -B scripts/verify.py --prepare`.

The additional pipeline builds the shared Lean project, regenerates untrusted
finite data from `Freiman/certificates/ray.json`, audits the new theorems, and
executes the root, finite-chain, and local checkers. It checks:

- 3,464,816 general-table rows through the existing verification pipeline;
- 10,088 arbitrary-root records and 2,073 adopted bands covering `[1/2,3/2]`;
- 454 spectral bounds and 4,234 finite-chain bands;
- four local conditions with 186 successors, including the initial interval;
- 24 deliberate corruptions across the four verification stages.

The exporters propose data only. Lean rechecks the exact rational/quadratic
arithmetic, automaton transitions, shape and derivative bounds, adoption,
coverage, and spectral inequalities. The generated records subdivide existing
certificate bands; they do not assert a new search result.

`logs/freiman-verification.json` records completion, acceptance summaries,
source/input/generated-data/log hashes, and axiom audit results. It is written
only after all stages pass. `RootReplay`, `FiniteReplay`, and `LocalReplay` are
execution drivers; they are not imported by the mathematical library.
