# Interior points of the Markov spectrum outside Hall's ray

**The Markov spectrum $M$ contains an interval of positive length strictly
below Hall's ray.** This project establishes

```math
[4.52578,4.52754]\subset M\cap(-\infty,c_F),\qquad
c_F=\frac{2221564096+283748\sqrt{462}}{491993569}.
```

Every point of $(4.52578,4.52754)$ is an interior point of $M$ outside
$[c_F,\infty)$. **The rational number $4.52666$ is one explicit example.**
The displayed decimal endpoints are exact rationals, and the interval has
width $11/6250=0.00176$.

The construction applies the closed successor cover for `31313`-avoiding tails
to fixed outward prefixes `(322,431)` with central digit 4, and bounds every
noncentral local value uniformly. The larger filled interval has endpoints
approximately `4.525777278415714…` and `4.527546990114258…`.

The result is supported by exact-arithmetic verification, a separate
implementation checking every adopted row, and a Lean proof connecting
checker acceptance to the claimed interval inclusion. It is an exhaustive
computer-assisted proof, rather than a numerical sample of spectral values.
See the [Lean verification guide](Lean/README.md) and the
[committed verification record](Lean/verification-baseline.json).

This construction uses `31313`-avoiding tails and subintervals $J_{p,q}$.
The original **interior-point construction for the `131`-forbidden set
$K_F+K_F$ remains unfinished**. Certificates from `stashed/` are not used.
The mathematical exposition is at the beginning of
[generalized_t.tex](doc/generalized_t.tex) (in Japanese).

## Construction and proof

Fix central digit 4 and outward prefixes $a=322$ and $b=431$. Append digits
from $\{1,2,3\}$, requiring each whole one-sided word to avoid `31313`.
The digit 4 already present in the fixed prefix 431 is allowed.

The convex hull of the corresponding sum of continued-fraction sets has
endpoints

```math
L_0=\frac{8512493+28004\sqrt{462}}{17339617},\qquad
H_0=\frac{1352829-8081\sqrt{462}}{2233974}.
```

The 25 verified root bands cover the subinterval with relative coordinates
$[1/16,7/8]$. After adding the central digit, the filled interval is

```math
\left[4+L_0+\frac{H_0-L_0}{16},\;
      4+L_0+\frac{7(H_0-L_0)}8\right]
\approx[4.525777278415714\ldots,4.527546990114258\ldots].
```

For every target point, the closed successor cover provides an indefinitely
extendible sequence of legal prefixes. Bounded derivative ratios force
continued-fraction denominators on both sides to grow. The underlying
compact cylinders are nested and shrink on both sides, realizing the
point by actual infinite continued fractions. Thus the proof passes from
finite parameter boxes to an entire real interval of realized values.

Every noncentral position has local value below the target interval.
The exact-arithmetic proof obtains

```math
\lambda_n\le\frac{4\sqrt{462}}{19}+\frac1{3025}
<4.525423<4.52578\qquad(n\ne0).
```

The Lean development proves the sufficient rational bound
$\lambda_n\le4525423/1000000$ uniformly over all legal tails and all nonzero
integer positions. The central value therefore equals the supremum of
all local values and belongs to $M$. Exact comparisons put the entire
claimed interval strictly below $c_F$.

## Lean verification

[Lean/README.md](Lean/README.md) describes the proof architecture, trust
boundary, and reproduction commands. The soundness theorem derives the
claimed inclusion from finite-checker acceptance, through interval filling
by actual infinite continued fractions and bounds on all noncentral values.
Compiled execution of the checker written in Lean accepted **all 3,464,816
original rows**. The 4,372 finite checks for the noncentral bound are computed
inside the Lean kernel.

Large-table acceptance is established by compiled execution. This is distinct
from an unconditional closed Lean theorem reducing that acceptance inside
the kernel. Final build, axiom audit, corruption tests, and exhaustive replay
are recorded in `Lean/logs/verification.json`; the committed baseline is
[verification-baseline.json](Lean/verification-baseline.json).

```sh
cd Berstein/Lean
python3 scripts/verify.py --prepare
```

See the guide for initial dependency setup. The formal statement concerns
$M$; no inclusion of this interval in $L$ or in $M\setminus L$ is claimed here.

## Rechecking the interval below Hall's ray

From the repository root:

```sh
python3 -B -S Berstein/src/verify_below_ray.py --full
```

This uses the Python 3 standard library and a C++17 compiler. It reads the
Freiman sources and saved tables without modifying them, and writes all
outputs under `Berstein/`. `--full` regenerates the algebraic input, requires
byte-for-byte agreement with the saved input, and **rechecks all 3,464,816
rows without deleting or modifying any row**. The recorded full run deleted
zero rows. Omitting `--full` reuses the verified table after checking input
and code hashes.

- The root derivative ratio satisfies `(51/50)^(-20) ≤ S ≤ (51/50)^(-19)`. The 25 adopted bands at this state pair cover `J_[1/16,7/8](322,431)`.
- The noncentral upper bound is `4√462/19 + 1/3025 = 4.525422212239698…`. It covers the fixed core, the first nine appended digits, and all remaining positions in the infinite tails.
- A separate rational calculation uses 40-digit extremal prefixes and terminal enclosure `[0,1]` to prove a bound below `4.525423`. It handles 242 legal five-digit windows and 57,054 nearby prefixes.
- Three negative controls remove endpoint bands or use an incorrect derivative-ratio box.

Results: [below_ray_verified.json](data/below_ray_verified.json).
Fixed root certificate: [below_ray_certificate.json](data/below_ray_certificate.json).
Full replay: [below_ray_kernel_replay.json](data/below_ray_kernel_replay.json).
Search: [search_freiman_bridge.py](src/search_freiman_bridge.py).
Floating-point candidate filtering during search is not used for proof acceptance.

## Verification by a separate implementation

The [independent audit record](audit/audit_verified.json) links the input,
coverage, spectral, and arithmetic checks. Here “independent” means a separate
implementation in this repository; it does not mean external peer review.

- `audit/independent_input.py` reconstructs quadratic-field values, legal transitions, exact endpoint identities, and constant tags without importing the original Python modules.
- `audit/independent_kernel.cpp` checks all 3,464,816 adopted rows using integer interval arithmetic and its own connectivity algorithm, without calling the original C++ checker. The recorded audit reports zero failed cells and no row deletion.
- `audit/independent_spectral.py` uses rational outer enclosures to check the root and noncentral bounds without importing either the original modules or the independent input checker.
- Negative controls test gaps, missing endpoints, missing child states and ratio boxes, and truncated input. A further 4,000 arithmetic comparisons check the C++ operations against Python `Fraction`.

The full [audit report](audit/REPORT.txt) is preserved in Japanese, with
reproduction commands at its end. These additional checks complement the
Lean soundness proof and document different ways of detecting implementation
errors; they do not eliminate the stated compiler/runtime trust boundary.

## Results for the separate `131`-forbidden problem

The rest of this README records a different problem and its search history.

1. The full-prefix version of `I(U,V;B1,B2)`, handling of empty terms, and calculation of extrema are defined. Child coverage, closure in an admissible family, and growth on both sides would imply interior points.
2. If both words end in 13 and have the same parity, a three-branch width ratio in `[5/6,6/5]` forces a genuine gap in the full convex hull. The key uniform estimate is `gap / width ≥ 16/9 - 8 sqrt(10)/45 > 6/5`. In particular, `[1.5358,1.5360]` lies in `conv(K_F(13)+K_F(13))` but not in the actual sum.
3. For the full-prefix convention with `B1={4,131,3}, B2={4,131}`, the three successors `(1,empty word),(2,empty word),(3,2)` exactly cover `I(112,122)`. **The induction does not close.** The interval `[1.295458,1.295459]` lies in the second child but is excluded from both `K_F(1122)+K_F(122)` and the root sum `K_F(112)+K_F(122)`. Retaining this root's entire T-interval is impossible.
4. For the same root, adding one forbidden word of length at most three on one side gives 39 cases: three are empty and the remaining 36 all contain that gap. Adding one word on each side gives 780 pairs: 120 are empty and 657 contain the same gap. Of the remaining three, two contain other gaps; only the two-sided binary type survives this finite exclusion test. This is not a proof of inclusion for that type.

None of these results implies that the entire set $K_F+K_F$ has empty
interior. The interval `[1.29288,1.292906]` considered in the earlier discussion
is different from the root gap above.

## Rechecking the `131` obstructions and search results

From the repository root, using the Python 3 standard library and a C++17 compiler:

```sh
python3 -B -S Berstein/src/check_all.py
```

This runs the small exact checks and positive/negative checker controls, then
collects completed search results. It does not automatically repeat the large
searches. See [verification_summary.json](data/verification_summary.json),
[obstructions.json](data/obstructions.json), [local_verified.json](data/local_verified.json),
and [forbidden_family_verified.json](data/forbidden_family_verified.json).
A separate implementation also cross-checked 1,896 endpoints and 820
empty-language decisions for the uniform generalized-T input. Ten checks
passed across the three checkers' controls and historical-violation flags.

## Direct search for generalized T-intervals

```sh
python3 -B -S Berstein/src/search_t.py --root 112,122 --length 3 --gap-depth 2 --output t_gap_filtered.json
python3 -B -S Berstein/src/search_t.py --root 112,122 --length 3 --gap-depth 3 --output t_gap3_filtered.json
```

`--length` is the total appended length on both sides. `--gap-depth` subdivides
each side to the specified depth and rejects candidates containing gaps in
the actual underlying Cantor sum. The forbidden-word types use the base
`{4,131}` and exchanged sums imposing one of `3,13,31,11,33` on one side.
At depth two, 33 of 814 candidates survive, giving local covers of binary and
13-forbidden types. At depth three, 16 remain; at depth four, six remain,
and these types with total appended length at most three can no longer cover
the target. This concerns the specified finite candidate family, not all
forbidden-word sets or longer successors.

The general API is [generalized_t.py](src/generalized_t.py). `Language` removes
states with no infinite extension. The numerical output of `generalized_t`
consists of **rational outer bounds on convex-hull endpoints**, not a proof
of interior points. [search_t.py](src/search_t.py) adds local-cover tests
using periodic-tail equalities and rational enclosures.

## Closure searches using shape, ratio, and interval position

Freiman's `graph_kernel.cpp` was adapted with newly generated input for
`131`-avoidance. The search partitions prefix shape, parity, forbidden-word
state, and ratio into finitely many boxes, then deletes rows that cannot be
covered. It checks both overlap inequalities, both parent endpoints, and
all boxes touched by the child's ratio image. Some coordinate systems use
auxiliary intervals wider than the forbidden-word T-intervals.

```sh
clang++ -O3 -std=c++17 Berstein/src/graph_kernel.cpp -o Berstein/bin/graph_kernel
python3 -B -S Berstein/src/prepare.py --name m2
Berstein/bin/graph_kernel Berstein/data/m2.dat Berstein/data/m2.json
```

Main saved configurations:

| Name | Suffix length | Ratio-grid base | Position subdivisions | Total appended length | Anchor |
|---|---:|---:|---:|---:|---|
| m2 | 2 | 11/10 | 32 | 3 + extremal branch length 4 | Lower endpoint |
| m3 | 3 | 11/10 | 64 | 3 | Lower endpoint |
| fine | 3 | 21/20 | 128 | 1 | Lower endpoint |
| golden | 3 | 21/20 | 128 | 2 | Golden ratio |
| centered | 3 | 21/20 | 128 | 2 | Golden-ratio center, derivative normalization |
| adaptive | 2–5 (shape width ≤ 1/100) | 11/10 | 32 | 2 | Golden ratio |
| golden_fine | 3 | 101/100 | 128 | 2 | Golden ratio |

Exact parameters are in `data/<name>.meta.json`, deletion histories in
`logs/<name>.log`, and completed results in `data/<name>.json`.
All seven searches ended with an empty family. Candidate retention is
bounded, so this does not prove the absence of interior points.

To repeat the final large configuration:

```sh
python3 -B -S Berstein/src/prepare.py --name golden_fine --memory 3 --length 2 --grid 128 --spine 0 --base 101/100 --low -280 --high 280 --root 112222,122222 --anchor golden
Berstein/bin/graph_kernel Berstein/data/golden_fine.dat Berstein/data/golden_fine.json
```

Only `--centered` input must be passed to a checker compiled from
`src/anchor_kernel.cpp`. If a closed table is found, pass its `.json.alive.bin`
as the third argument to the same executable and recheck every row without
protected rows. Membership and positive length of a concrete root interval
must then be established before concluding that interior points exist.
Success on an artificial positive control is not success for `131`-avoidance.

The next task for this separate approach is to exclude T-intervals containing
genuine gaps from the admissible family, and obtain a family to which every
chosen successor returns. Proved obstructions and unsuccessful searches have
different meanings.

Coarse shape boxes are another issue. The three-digit box ending in 111 has
width `11/322 ≈ 0.0342`. `--shape-tolerance 1/100 --memory 2` subdivides only
suffixes with excessive width. This yields 30 suffixes and 60 states including
parity; 724 child-shape inclusions were checked exactly. The coarse-ratio
search with this subdivision still did not close.

`golden_fine` also **became empty after 20 deletion iterations, starting from
194,168,832 rows**. Thus all seven configurations above are complete.

Uniform tables for additional forbidden words under the full-prefix
convention need historical-violation flags. For example, 11221 and 13221
have the same parity, last three digits, and `131` state, but only the former
is eligible when 13 is forbidden. `generalized_t.py` and `search_t.py`
preserve this distinction by checking the entire word.

## Uniform search retaining forbidden-word T-endpoints directly

`prepare_t.py` / `t_kernel.cpp` track five types directly: F, the exchanged
sum T, left binary, right binary, and both binary. F, T, and both binary are
symmetric generalized T-intervals; the one-sided binary types are auxiliary
intervals with only one term. A flag records whether a 3 has occurred,
correctly excluding binary terms that are empty under the full-prefix
convention. Extrema lie in `Q(sqrt(3),sqrt(10))`; ratios use derivatives at the
binary set's lower endpoint. Returns toward periodic words 12/21 on both
sides are also candidates.

```sh
clang++ -O3 -std=c++17 Berstein/src/t_kernel.cpp -o Berstein/bin/t_kernel
python3 -B -S Berstein/src/prepare_t.py --name t_fine --memory 3 --base 51/50 --low -140 --high 140 --root 112222,122222
Berstein/bin/t_kernel Berstein/data/t_fine.dat Berstein/data/t_fine.json
```

Both the coarse `t_kernel` configuration (206,180 rows) and the fine `t_fine`
configuration (6,496,720 rows) became empty. **No nonempty closed admissible
family for iteration was obtained in these searches.** Both use finite
candidate lists and sufficient conditions; they do not rule out every
approach using generalized T-intervals.
