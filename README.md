# Verify Freiman Constant

This repository develops rigorous, reproducible computational verification
of Freiman's constant and Hall's ray. The current construction proves
$[c_F,\infty)\subset M\cap L$ using exact finite certificates and an argument
with infinite continued fractions. Optimality of the endpoint $c_F$ is
outside the scope of the current proof. See [Freiman/](Freiman/README.md)
for the proof and reproduction instructions.

A related result establishes **$[4.52578,4.52754]\subset M\cap(-\infty,c_F)$**,
giving explicit interior points of the Markov spectrum outside Hall's ray.
It is supported by exact-arithmetic checks, a separate verifier implementation,
and Lean-proved checker soundness with exhaustive compiled certificate
verification. See [Markov_interior/README.md](Markov_interior/README.md) for the result,
construction, verification evidence, and trust boundary.

## Code: start here

From the repository root:

```sh
# Complete Freiman-ray verification, including the full finite table.
python3 -B -S Freiman/verify.py

# Complete interior-interval verification.
python3 -B -S Markov_interior/verify.py
```

### The complete interior-interval proof

[Markov_interior/](Markov_interior/README.md) is self-contained: copy that whole
directory elsewhere and run `python3 -B -S verify.py`. It needs only the Python
standard library and a C++17 compiler.

| Source | Responsibility |
|---|---|
| [verify.py](Markov_interior/verify.py) | Default end-to-end verification of the three interval claims |
| [proof.py](Markov_interior/proof.py) | Actual root coverage, all-position bounds, periodic endpoints and finite gluing obligations |
| [prepare.py](Markov_interior/prepare.py) | Exact numeric input generation for both languages |
| [kernel.cpp](Markov_interior/kernel.cpp) | Deletion search and fixed-table replay |
| [audit.py](Markov_interior/audit.py) | Independent input semantics, checked every run |
| [audit.cpp](Markov_interior/audit.cpp) | Optional separate exhaustive coverage implementation |

The infinite arguments are in [PROOF.md](Markov_interior/PROOF.md), and all
required inputs are in [certificates/](Markov_interior/certificates/README.md).
The default verifier checks both full tables and the original paper's 25 bands,
then root coverage, uniform noncentral bounds and all three interval inclusions.
`--tables-only` is the explicit narrower mode and emits no interval claim.
The [format guide](Markov_interior/FORMAT.md) includes the complete record layout.

Archived implementations and experiment logs are not dependencies of this proof.
The shared [Lean project](Lean/README.md) separately handles the existing formal
original-interval result.

### The complete Freiman-ray proof

[Freiman/](Freiman/README.md) contains the compact implementation and fixed
certificates; its mathematical proof is in the root [doc/](doc/README.md).
To run elsewhere, copy both `Freiman/` and `doc/` under one parent, then run
`python3 -B -S verify.py` inside `Freiman/`. The verifier also hashes the TeX paper.

| Source | Responsibility |
|---|---|
| [verify.py](Freiman/verify.py) | Default end-to-end verification of the ray |
| [proof.py](Freiman/proof.py) | Four local endpoint conditions, entry covers, all-position bounds, and the ray chains |
| [prepare.py](Freiman/prepare.py) | Exact continued-fraction arithmetic and numeric input generation |
| [kernel.cpp](Freiman/kernel.cpp) | Deletion search and fixed-table replay |
| [audit.py](Freiman/audit.py) | Independent input semantics, checked every run |
| [audit.cpp](Freiman/audit.cpp) | Optional separate exhaustive coverage implementation |

The fixed inputs are the four files in
[certificates/](Freiman/certificates/README.md). The original general table and
ray certificate bytes are preserved. The finite row universe is 4,801,280
parameter-box conditions, of which 3,464,816 are adopted.
[TABLE_FORMAT.md](Freiman/TABLE_FORMAT.md) explains the input and adoption array.

```sh
# Full ray proof, additionally checking every row with the separate C++ implementation.
python3 -B -S Freiman/verify.py --independent --output /tmp/freiman-proof.json

# Only the general table, including exact input regeneration; no ray claim.
python3 -B -S Freiman/verify.py --table-only
```

The whole-ray proof also checks 186 local successors, 379 successors for
34 entry covers, 136 initial bands and 91 noncentral-bound cases.
The infinite iteration, Markov realization and Lagrange gluing are in
the [paper](doc/out/lemma2_schecker.pdf), with the code correspondence in Appendix A.
Builds and intermediate reports use a temporary directory; cached success flags
are not proof inputs. The current directory has no `src/`, role subpackages,
launcher, historical experiments, or generated executables.

To search the finite universe, compile [kernel.cpp](Freiman/kernel.cpp) and omit
the adoption array. See the [commands and scope](Freiman/README.md#入力と探索).
Historical root/menu discovery, protected-seed expansion, and earlier files are
retained in Git commit `2ac2b5e20dedd8255954c5a32f5694649defd771`. They are not
dependencies of either current analytic proof and are omitted from the current tree.

### Interval proof versus table closure

The current [interval proof](Markov_interior/PROOF.md) contains both parts.
Closed covers realize every point of admitted initial bands by actual infinite
continued fractions. The root and noncentral checks make the central value the
supremum at all positions, proving Markov membership. Periodic-block gluing and
the checked positive margins give Lagrange membership. All are part of the
default `Markov_interior/verify.py` result.

The [Lean development](Lean/Berstein/README.md) concerns the original
3,464,816-row table and original interval. The extended table and endpoints have
not been added to that formalization. A failed bounded search does not establish
nonexistence.

## Introduction

For an irrational number $\alpha$, define

```math
\ell(\alpha)= \limsup_{q\to\infty}\frac{1}{q\|q\alpha\|},
```

where $\|x\|$ denotes the distance from $x$ to the nearest integer.

The Lagrange spectrum is

```math
L = \{\ell(\alpha) < \infty: \alpha\in\mathbb{R}\setminus\mathbb{Q}\}.
```

Hall [^hall] proved that $L$ contains a half-line extending to infinity, now called Hall's ray. Freiman [^freiman] later showed that the initial point of this ray is

```math
c_F = [4;4,3,2,2,\overline{3,1,3,1,2,1}] + [0;3,2,1,1,\overline{3,1,3,1,2,1}] = \frac{2221564096 + 283748\sqrt{462}}{491993569} \approx 4.52782956616087914088\ldots,
```

now known as Freiman's constant.

For a bi-infinite sequence $a\in\mathbb Z_{>0}^{\mathbb Z}$, write

```math
\lambda_n(a)=[a_n;a_{n+1},a_{n+2},\ldots]+[0;a_{n-1},a_{n-2},\ldots],\qquad
M=\left\{\sup_{n\in\mathbb Z}\lambda_n(a)<\infty:
 a\in\mathbb Z_{>0}^{\mathbb Z}\right\}.
```

## Repository map

| Directory | Contents |
|---|---|
| [doc/](doc/README.md) | Shared mathematical papers: the Freiman ray and interior Markov intervals |
| [Freiman/](Freiman/README.md) | Schecker-style computer-assisted proof of $[c_F,\infty)\subset M\cap L$, with exact certificates and reproduction instructions |
| [Markov_interior/](Markov_interior/README.md) | Complete interval proof, including both tables, root coverage and noncentral bounds |
| [Lean/](Lean/README.md) | Shared formal-verification workspace, currently including the original interior-interval checker and proof |
| [Schecker/](Schecker/README.md) | SageMath discovery notebooks and investigation of classical successor lists |
| [misc/](misc/README.md) | Supporting numerical calculations for classical proofs |

The English READMEs explain the results, evidence, and reproduction steps.
Detailed Freiman notes and the original TeX/audit expositions are in Japanese.

## Classical discovery notebooks

The following notebooks use [SageMath](https://www.sagemath.org/).

### `Schecker/`

Notebooks implementing and extending the method of Schecker [^schecker], who proved that $[\sqrt{21},\infty)\subset L$.

- **`schecker_proof_1.ipynb`** — Core search for admissible bilateral continued-fraction intervals.
  - Represents words as $A=(a_{-h},\ldots,a_{-1}\mid a_0,a_1,\ldots,a_k)$ and tests Schecker's admissibility condition (*zulässig*) via the $T$-ratio.
  - For each admissible pair, computes the corresponding $T$-interval, the maximum Lagrange values, and the resulting candidate subinterval of the Lagrange spectrum.
  - Exhaustively enumerates such pairs up to a chosen depth and merges overlapping intervals.
  - Includes precomputed runs for depths $7$–$12$; at depth $\ge 11$ the merged components stabilize at $[4.582\ldots,6.655\ldots]$ and $[6.655\ldots,6.656\ldots]$, consistent with $\sqrt{21}\approx 4.582\ldots$.

- **`schecker_proof_2.ipynb`** — Investigation of Lemma 2 from Schecker's paper and of the auxiliary lemmas (*Hilfssätze*) used in its proof.
  - Tests the proposed successor lists and their admissibility and connectivity ranges.
  - Records problems in the stated successor lists and auxiliary formulae.
  
- **`schecker_proof_3.ipynb`** — Direct automated search for short admissible 3-successors covering a given T-interval.
  - Computes T-intervals, T-ratios, and all admissibility conditions directly from the definitions, without relying on Lemma 2 or Hilfssatz 4.
  - Enumerates successors in increasing total suffix length and finds a minimum-cardinality interval cover at the first successful depth.
  - Supports exhaustive finite surveys of all admissible base intervals with bounded total depth, grouped by parity, observed T-ratio range, and successor-cover type.
  - Uses high-precision numerical arithmetic for discovery; proof candidates still require exact or interval-arithmetic certification.

### `misc/`

Supporting calculations for classical proofs.

- **`hall_proof.ipynb`** — Numerical checks of inequalities used in Hall's proof [^hall].
  - For each of the three interval types, computes lower bounds on the ratios $|M_1|/|I|$ and $|M_2|/|I|$ that appear as lemmas in the argument that certain sums of continued-fraction Cantor sets cover an interval.

- **`freiman_judin_proof.ipynb`** — Numerical checks of inequalities used in the proof of Freiman and Judin [^freiman-judin].
  - Implements a function `ratio_of_intervals` that bounds $|A|/|B|$ when $A$ and $B$ are continued-fraction intervals sharing a common prefix.
  - Applies it to the type-1 and type-2 interval decompositions and verifies that each removed subinterval is shorter than the remaining interval.

## References

[^hall]: Hall, M. (1947). On the sum and product of continued fractions. *Annals of Mathematics*, 48(4), 966–993.

[^freiman]: Freiman, G. A. (1975). *Diophantine Approximations and the Geometry of Numbers (Markov's Problem)*. Kalinin State University Press. In Russian.

[^freiman-judin]: Freiman, G. A., & Judin, A. A. (1966). On the Markov spectrum (Russian). *Litovsk. Mat. Sb.*, 6, 443–447.

[^schecker]: Schecker, H. (1977). Über die Menge der Zahlen, die als Minima quadratischer Formen auftreten. *Journal of Number Theory*, 9(2), 121–141.
