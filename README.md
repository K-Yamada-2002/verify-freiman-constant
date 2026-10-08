# Verified interior points below Hall's ray

**This repository establishes an explicit interval of the Markov spectrum
strictly below Hall's ray:**

```math
\boxed{[4.52578,4.52754]\subset M\cap(-\infty,c_F)},\qquad
c_F=\frac{2221564096+283748\sqrt{462}}{491993569}
\approx4.527829566160879.
```

The decimal endpoints are exact: $4.52578=226289/50000$ and
$4.52754=226377/50000$. Thus every point of $(4.52578,4.52754)$ is an interior
point of $M$ outside $[c_F,\infty)$, in the ordinary topology of $\mathbb R$.
**One explicit example is $4.52666$; the interval has width $11/6250=0.00176$.**

This is a rigorous computer-assisted proof with a **Lean-checked soundness
argument and exhaustive verification of the finite certificate**. The
construction realizes every value in the interval by an actual bi-infinite
continued fraction, and bounds all noncentral positions uniformly. Its
conclusion is not based on sampling or floating-point agreement.

| Verification layer | Evidence |
|---|---|
| Exact certificate verification | All **3,464,816** adopted rows checked without deletion; exact endpoint and ratio comparisons |
| Separate implementation | An independent implementation of input semantics, full-table coverage, and spectral bounds, with negative controls |
| Lean soundness proof | Checker acceptance implies the interval inclusion and nonempty interior; **4,372** finite spectral checks computed in the kernel |
| Execution and axiom audit | All **484** state pairs accepted by the compiled Lean checker; six corrupted inputs rejected; only standard Lean/Mathlib axioms |

**Trust boundary:** the mathematical soundness theorem is kernel-checked;
acceptance of the concrete large table is established by compiled Lean
execution, which also trusts the compiler, runtime, and input handling. This
is not an unconditional closed theorem reducing all 3.46 million rows inside
the kernel. The [verification guide](Berstein/Lean/README.md) and
[committed baseline](Berstein/Lean/verification-baseline.json) make that
boundary explicit. “Independent implementation” describes code in this
repository, not external peer review.

Start with the [result and construction](Berstein/README.md) and the
[Lean verification guide](Berstein/Lean/README.md). The result concerns this
explicit interval in **$M$**. Inclusion of this interval in $L$ or in
$M\setminus L$ is not asserted.

## Reproduce the main result

From a fresh checkout, with the pinned Lean toolchain and a C++17 compiler:

```sh
cd Berstein/Lean
lake update
lake exe cache get
python3 scripts/verify.py --prepare
```

This builds the proofs and checker, audits axioms, generates witnesses,
replays all adopted rows, and checks rejection of corrupted inputs. See the
[guide](Berstein/Lean/README.md) for verification using existing artifacts.
`lake build` alone does not perform the exhaustive replay.

The original exact-arithmetic route can be run from the repository root:

```sh
python3 -B -S Berstein/src/verify_below_ray.py --full
```

## Repository map

| Directory | Result and status |
|---|---|
| [Berstein/](Berstein/README.md) | Explicit interior interval below Hall's ray; exact certificates, separate audit implementation, and Lean verification |
| [Freiman/](Freiman/README.md) | Schecker-style computer-assisted proof of $[c_F,\infty)\subset M\cap L$; optimality of $c_F$ is not proved here |
| [Schecker/](Schecker/README.md) | SageMath discovery notebooks and investigation of classical successor lists |
| [misc/](misc/README.md) | Supporting numerical calculations for classical proofs |

The English READMEs explain the results, evidence, and reproduction steps.
Detailed historical Freiman notes and the original TeX/audit expositions
remain in Japanese. The separate search for interior points of the
`131`-forbidden set $K_F+K_F$ is unfinished; it is not the construction behind
the verified `31313`-based result above.

## Mathematical background

For a bi-infinite sequence $a\in\mathbb Z_{>0}^{\mathbb Z}$, write

```math
\lambda_n(a)=[a_n;a_{n+1},a_{n+2},\ldots]+[0;a_{n-1},a_{n-2},\ldots],\qquad
M=\left\{\sup_{n\in\mathbb Z}\lambda_n(a)<\infty:
 a\in\mathbb Z_{>0}^{\mathbb Z}\right\}.
```

This is the continued-fraction definition used by the Lean development.

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

The repository began as a project to make the intricate computations behind
Freiman's ray accessible to exact computational verification. It now also
contains the separate interior-interval result stated above.

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
