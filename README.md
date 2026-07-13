# Verify Freiman Constant

This repository aims to verify that Freiman's constant is the initial point of Hall's ray. The project is a work in progress.

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

However, Freiman's original proof relies on over one hundred pages of intricate computation. The source is also difficult to access, and the argument has not been available in a form that can be checked independently and computationally.

The goal of this repository is to develop an automatic and rigorous algorithm for computing the initial point of Hall's ray.

## Current Contents

All notebooks are written for [SageMath](https://www.sagemath.org/).

```text
.
├── Schecker/
│   ├── schecker_proof_1.ipynb
│   └── schecker_proof_2.ipynb
├── misc/
│   ├── hall_proof.ipynb
│   └── freiman_judin_proof.ipynb
├── LICENSE
└── README.md
```

### `Schecker/`

Notebooks implementing and extending the method of Schecker [^schecker], who proved that $[\sqrt{21},\infty)\subset L$.

- **`schecker_proof_1.ipynb`** — Core search for admissible bilateral continued-fraction intervals.
  - Represents words as $A=(a_{-h},\ldots,a_{-1}\mid a_0,a_1,\ldots,a_k)$ and tests Schecker's admissibility condition (*zulässig*) via the $T$-ratio.
  - For each admissible pair, computes the corresponding $T$-interval, the maximum Lagrange values, and the resulting candidate subinterval of the Lagrange spectrum.
  - Exhaustively enumerates such pairs up to a chosen depth and merges overlapping intervals.
  - Includes precomputed runs for depths $7$–$12$; at depth $\ge 11$ the merged components stabilize at $[4.582\ldots,6.655\ldots]$ and $[6.655\ldots,6.656\ldots]$, consistent with $\sqrt{21}\approx 4.582\ldots$.

- **`schecker_proof_2.ipynb`** — Verification of Lemma 2 from Schecker's paper, which states that certain successor intervals are admissible and that their union is connected, using the auxiliary lemmas (*Hilfssätze*) established there.
  - verifying simplified version of Lemma 2, which is sufficient to prove Lemma 1.
  - Lemma 2 in Schecker's paper is correct, but seems not suitable to verify by using Hilfsätze. Schecker may have made some mistake.
  - Also, Hilfssätze stated in the paper contain some mistakes in signs. Documentation for error correction will be added later.
  
- **`schecker_proof_3.ipynb`** — Automated search and verification of proposition ike Lemma 2.
  - work in progress

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