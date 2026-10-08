# A Schecker-style proof of the Freiman ray

This directory proves **`[c_F, ∞) ⊂ M ∩ L`** using successor covers with the
forbidden word `31313`. The proof combines finite exact-arithmetic verification
with a mathematical argument constructing infinite continued fractions.

For the separate result on **interior points below Hall's ray**, see
[Berstein](../Berstein/README.md) and its [Lean verification](../Berstein/Lean/README.md).
The half-line proof documented here does not itself establish optimality of $c_F$.

Start with the [TeX exposition](doc/lemma2_schecker.tex) or
[PDF](doc/lemma2_schecker.pdf), both in Japanese. Following the Schecker
exposition, it presents preliminaries, realization of central values by
successor covers, passage to $M$ through noncentral bounds, admissibility,
construction of the ray from initial intervals, and finite verification of
the covering lemma. It includes an actual three-successor cover and states
inclusion in $L$ as a separate final corollary. It also explains the
correspondence with Schecker's T-intervals and the passage from Lemma 2 to
the cover required by Lemma 1.

The redesign of October 1, 2026 uses the same intervals `J_{p,q}(a,b)`
throughout. Special families carrying an ancestor and iteration count were
replaced by conditions on four rational parameters of the current state.
The derivative ratio `V_zeta` is invariant under appending 33 to both sides.
The endpoint equality condition `S=S_*` is no longer needed. There is now
only one general family, `graph_wide`, with 34 initial entry covers for
short words. Its 3,464,816 rows are parameter boxes checked by one finite
algorithm, partitioning left/right states, ratio ranges, and subinterval
positions. They are not millions of separately written mathematical proofs.
The current priority is a clear algorithm and rigorous replay, rather than
reducing the number of conditions below 1,000.

The general table was found by deletion search over a wider ratio range,
protecting a verified narrow-range table as a seed. The final verification
checks every row, including the seed, without protection. The proof uses
this final verification.

## Layout

| Directory | Contents |
|---|---|
| `doc/` | TeX/PDF exposition, proof details, complete interval tables, audits, and search history; detailed documents are in Japanese |
| `src/` | Python and C++ verification, search, and table-generation programs |
| `data/` | Fixed certificates, inputs, verification results, and historical search results |
| `logs/` | Execution logs |
| `bin/` | Generated, platform-dependent C++ executables |

Historical search results are retained in `data/` for reproducibility. The
proof uses the fixed certificates and their verification results listed
below. Filenames or search success flags alone do not establish completion.

## Reverification

Python 3 with its standard library and a C++17 compiler are required. From
the repository root:

```sh
python3 -B -S Freiman/src/verify_unified_proof.py --full
```

This regenerates the general-family input, compiles `bin/graph_kernel_verify`,
and verifies closure of all 3,464,816 rows, 186 successors for four local
conditions, 379 successors for 34 entries, 136 initial-cover bands, and
91 noncentral-bound cases. The new proof does not read `graph_m2` data.
Results are saved to [unified_proof_verified.json](data/unified_proof_verified.json);
the fixed certificate is [unified_proof_certificate.json](data/unified_proof_certificate.json).

Omit `--full` to reuse a full-table verification after matching input and
code hashes. Run with `--full` after changing code or fixed input. Scripts
are independent of the working directory; bare output filenames such as
those passed to `--output` are resolved under `data/`. Direct C++ invocations
require explicit input/output paths. Some search programs require NumPy;
exact reverification does not.

## Main documents and certificates

The detailed documents below are in Japanese; this README provides the English
entry point and reproduction instructions.

- [Mathematical exposition](doc/lemma2_schecker.tex): definitions, theorems, proofs, and correspondence with Schecker.
- [Complete initial-cover table](doc/HALL_RAY_INITIAL_COVER.md): root and band endpoints are unchanged in the new construction.
- [Construction of the general family](doc/INVARIANT_SEARCH.md).
- Earlier construction: [ray proof](doc/HALL_RAY_PROOF.md), [endpoint lemma](doc/ENDPOINT_LEMMA.md), and [complete endpoint successor lists](doc/ENDPOINT_MENUS.md).
- [Audit record](doc/PROOF_AUDIT.md).
- [Original search design](doc/SEARCH_DESIGN.md) and [search history](doc/RESULTS.md).

The current fixed inputs are `data/unified_proof_certificate.json` and the
`.dat`, `.meta.json`, and `.json.alive.bin` files for `graph_wide`.
The current verifier treats returns to the same local conditions and entry
into the general family as a single Lemma-2-style successor cover.
Verification hashes cover both sources and data; `src/layout.py` resolves
the current layout.

Earlier proofs are retained. The earlier exposition is
`doc/archive/lemma2_schecker_20260929.tex`; the version preceding the October 1
redesign is `doc/archive/lemma2_schecker_20261001_compact.tex`.
The earlier construction is fully checked by `src/verify_hall_ray.py --full`.
`src/audit_schecker_proof.py` is a separate supplementary check of its fixed
interval tables; it does not replace uniform closure verification for the
new local conditions.

The separate verification components of the redesign are
`src/local_invariant_returns.py`, checking ancestor-free invariants under
appending 33, and `src/wide_bootstrap_verify.py`, checking finite entries
into the single general family. `src/make_unified_certificate.py` combines
these fixed menus into the current certificate. Its output is not certified
until accepted by `src/verify_unified_proof.py`.

To regenerate the initial interval tables:

```sh
python3 -B Freiman/src/write_hall_tables.py
```

Compile `doc/lemma2_schecker.tex` with the built-in LaTeX editor or XeLaTeX.
The result here is half-line inclusion; optimality of $c_F$ is outside its scope.

## Historical compression searches (October 1, 2026)

These searches addressed an earlier target of at most 1,000 conditions,
which is no longer the project's objective. They are separate from the fixed
certificates and are not required for the current proof or its verification.
The original row counts measure parameter boxes, not the minimum number of
mathematically independent conditions.

Preserving the tables exactly, merging consecutive ratio boxes and types,
and using left/right symmetry gives 12,685 entries for `graph_m2` and 12,113
for `graph_wide`. The [compression record](data/admissibility_compression_summary.json)
checks byte-for-byte reconstruction. Further grouping distinct `graph_wide`
state pairs with identical ratio and type intervals gives 6,912 entries.
This still does not yield a proof with a small number of successor lists.

There is also a lower bound for a restricted representation: each condition
fixes the left/right states, restricts `S` to a single interval, and selects
types independently of `S`. If an adopted range for one type has `n`
components, that state pair alone needs at least `n` conditions. Taking the
maximum over types for each state pair and summing modulo left/right symmetry
gives **2,880** for `graph_m2` and **1,779** for `graph_wide`.
These are bounds **for exact preservation of the current tables**. They do
not exclude other admissible families, inequalities coupling `S` and type,
or conditions grouping multiple state pairs.
The [bounds and interval lists](data/admissibility_rectangle_bound.json)
can be regenerated with:

```sh
python3 -B -S Freiman/src/admissibility_rectangle_bound.py
```

New families selected from small numbers of rectangles were also tested.
Candidates with 759 conditions, 990 conditions, and 990 overlapping
conditions became empty when rows not covered by the chosen successors were
deleted. Searches with ratio-grid steps enlarged by factors of 4, 8, and 16
also became empty. These are failures of the selected searches, not proofs
that mathematical covers do not exist: the searches bound the retained
successor candidates and intersection-graph data.

Relevant programs are `src/search_small_family.py`, `src/prepare_coarse_search.py`,
and `src/graph_kernel_reduce.cpp`. Proposals are `data/small*_proposal.json`,
results are `data/small*.json` and `data/coarse_s*.json`, and logs are in
`logs/`. Conditions marked `proposal_only` are not verified admissible
families. See [small_family_search_summary.json](data/small_family_search_summary.json)
for all six experiments.

A search coarsening two-digit suffixes to one digit reduced the one-sided
states from 22 to 12. The initial common portion retained 98.7% of the
original rows, but the closure search with the coarser states became empty.
It produced no new admissible family. The
[verification method and scope of failure](data/simple_family_m1_report.json)
are recorded separately.
