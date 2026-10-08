# Interior points of the Markov spectrum outside Hall's ray

**A Lean proof of checker soundness, with exhaustive certificate verification.**

The Markov spectrum $M$ contains an interval of positive length strictly below
Hall's ray $[c_F,\infty)$. The verified inclusion is

```math
[4.52578,4.52754]\subset M\cap(-\infty,c_F),\qquad
c_F=\frac{2221564096+283748\sqrt{462}}{491993569}.
```

Consequently, in the usual topology of the real line,

```math
(4.52578,4.52754)\subset
\operatorname{int}_{\mathbb R}\!\left(M\setminus[c_F,\infty)\right).
```

**In particular, $4.52666$ is an explicit interior point of $M$ outside Hall's ray.**
The interval has exact width $0.00176=11/6250$.

Lean proves the implication from certificate acceptance to this interior-point
result. Compiled execution of the checker accepted **all 3,464,816 rows** of
the original table. The recorded final build, axiom audit, exhaustive replay,
and six corruption tests all succeeded. The committed record is
[verification-baseline.json](verification-baseline.json); a new run writes
`logs/verification.json`.

## Verification method

The construction uses tails avoiding `31313`, fixed outward prefixes `(322,431)`,
and central digit 4. The 4 in the fixed prefix `431` is allowed; only appended
digits are restricted to 1, 2, and 3. This is separate from the unfinished
interior-point construction for the `131`-forbidden set.

For the large table, we **execute a checker whose mathematical soundness has
been proved in Lean**. The sole premise of `Berstein.target_interval_subset`
in [Berstein/Main.lean](Berstein/Main.lean) is
`Certificate.check input data alive cells = true`. Interval filling,
noncentral bounds, endpoint semantics, and successor coverage are proved
rather than left as mathematical assumptions.

```lean
theorem target_interval_subset
    (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (h : Certificate.check input data alive cells = true) :
    Set.Icc targetLower targetUpper ⊆ markovSpectrum ∩ Set.Iio freimanConstant
```

The same acceptance condition yields `open_interval_subset_interior` and
`interior_below_freiman_nonempty`. The explicit interior point is the midpoint,
$226333/50000=4.52666$.

**The concrete acceptance of the 3.46-million-row table is not reduced inside
the Lean kernel to obtain an unconditional closed theorem.** The kernel checks
the soundness proof; compiled execution establishes acceptance of the concrete
certificate. This execution also trusts the Lean compiler, runtime, and file
input. No external program's success flag is introduced as an axiom.

This is a rigorous computer-assisted proof with a formally verified soundness
argument and exhaustive execution evidence. Its strength is documented by
checkable obligations, not by a numerical probability of correctness.

## Reproduction

Lean **4.32.1** and Mathlib **v4.32.1** are pinned. To obtain dependencies on a
fresh checkout:

```sh
cd Berstein/Lean
lake update
lake exe cache get
```

To generate the certificates, build the proofs and checker, audit axioms,
replay the entire table, and confirm rejection of corrupted inputs:

```sh
python3 scripts/verify.py --prepare
```

To replay the entire table using already generated certificates:

```sh
python3 scripts/verify.py
```

To reuse a successful exhaustive replay only after checking the hashes of the
executable, original input, adoption bitmap, all 484 certificates, and logs,
while rerunning the proof build, axiom audit, and corruption tests:

```sh
python3 scripts/verify.py --reuse-replay
```

The full replay uses four parallel shards by default. In the recorded run,
each shard took about 12 minutes; this is not a runtime guarantee for other
machines. Use `lake build` to build only the proofs and `lake env lean Audit.lean`
to print the axioms. **`lake build` alone does not replay the whole table.**
There is no runtime dependency on a neighboring `hall-ray` checkout.

## How the proof fits together

| Stage | Main modules and obligations |
|---|---|
| Real-number semantics | `Markov`, `Forbidden31313`, `CFInvariant`: bi-infinite continued fractions, the five-state forbidden-word automaton, and rigorous bounds on infinite tails |
| Input validation | `Quadratic462`, `QuadraticCF`, `SemanticCheck`, `SemanticSound`: quadratic-field arithmetic, exact endpoint-ID equalities, words, states, parity, and constant tags |
| Uniform bounds over boxes | `Normalization`, `FractionalLinear`, `SemanticTransport`, `GraphNumericSound`: normalized continued-fraction differences, shape ratios, and derivative multipliers over entire real intervals |
| Finite-table coverage | `GraphCertificate`, `GraphCertificateFacts`: rational comparisons, interval chains, all adopted rows and destinations, and coverage by ratio boxes |
| Passage to infinite sequences | `ActualCylinders`, `CylinderCover`, `GraphState`, `GraphSuccessor`: actual prefixes, nonempty compact cylinders, nesting, shrinking on both sides, and realization of every covered point |
| Initial interval | `RootFacts`, `RootCheck`, `RootState`: endpoint sums and ratio for prefixes 322 and 431; the 25 initial bands fill the required interval |
| Central dominance | `SpectralVerified`: `localValue ≤ 4525423/1000000` for every legal tail and every noncentral position; 4,372 finite checks proved using `decide +kernel` |
| Main result | `CertificateCheck`, `Verified`, `Main`: certificate acceptance implies spectral membership of the interval and existence of interior points |

The noncentral bound combines finite checks near the core with six inward
digits and automaton bounds for distant positions. The original informal
replacement argument is not imported as an unproved premise.

Constant tags are checked by exact quadratic-field identities, not by overlap
of approximate enclosures. At ratio boundaries, the proof establishes that a
verified box can be chosen; it does not assume that every touching box is
adopted. Finite graph closure is connected to actual shrinking
continued-fraction cylinders before interval filling is concluded.

## Original data and execution records

The checker reads `Freiman/data/graph_wide.dat` and
`Freiman/data/graph_wide.json.alive.bin` directly. The fixed table is not
replaced by a smaller table obtained by deleting rows that fail verification.

| Item | Count |
|---|---:|
| One-sided states | 22 |
| State pairs | 484 |
| Adopted cells | 150,040 |
| Adopted rows | 3,464,816 |
| Selected child vertices | 799,932 |
| Total coverage-path vertices | 6,541,897 |

The initial rows are the 25 bands numbered 3–27, at state pair 193 and ratio
box 135. A different root index in the saved graph header is not substituted
for these initial rows.

- `scripts/export_graph.cpp`: an untrusted exporter of finite coverage witnesses from the search output.
- `scripts/export_semantics.py`: an untrusted generator of exact endpoint labels and related data in `Berstein/Data/Meaning.lean`.
- `graphReplay`: the Lean executable checking input semantics, the root, prepared interval operations, and coverage for every geometry.
- `generated/replay_report.json`: shard exit codes, ranges, counts, and hashes of inputs, the executable, certificates, and logs.
- `logs/verification.json`: the combined record of final-theorem axioms, Lean source hashes, exhaustive replay, and corruption tests.

`NegativeControls.lean` creates six corruptions in memory without changing the
original files. It tests the root adoption bit, an exact endpoint value, a
used constant, a cell, an adopted row's coverage path, and a selected
destination mask.

## Trust boundary

`Audit.lean` lists the axioms of the main theorems. The verification script
fails if any axiom other than the standard Lean/Mathlib `propext`,
`Classical.choice`, and `Quot.sound` occurs. The proof uses no `native_decide`,
`sorry`, `admit`, or additional mathematical axioms. Hashes establish the
identity of inputs and execution artifacts; they do not replace mathematical
soundness.

`markovSpectrum` is defined using bi-infinite sequences of positive integer
partial quotients and the supremum of their local values. The excluded ray
is explicitly `Set.Ici freimanConstant`. Equivalence with a definition using
quadratic forms, and the classical theorem identifying this constant as the
smallest possible ray endpoint, are separate from this formalization.
This result asserts membership in $M$; it does not assert that the displayed
interval lies in $L$ or in $M\setminus L$.

`HallRay/Basic.lean` and `HallRay/ContinuedFraction/{Basic,Mobius}.lean` were
vendored from [hall-ray](https://github.com/K-Yamada-2002/hall-ray), commit
`a584e5620124d23c709e3bbdc66db8b8b0586310`. The MIT license is in
`HallRay/LICENSE`; hashes of source materials and vendored files are in
`sources.json`.
