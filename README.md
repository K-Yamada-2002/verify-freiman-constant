# verify-freiman-constant

This project aims to verify, in a reproducible computer-assisted way, whether Freiman's constant is the left endpoint of Hall's ray in the classical Lagrange spectrum.

## Goal

The Lagrange spectrum `L` records the possible values of a Diophantine approximation constant. Hall proved that `L` contains a half-line extending to infinity, now called Hall's ray. Freiman later claimed to determine the left endpoint of the maximal such half-line.

The endpoint is Freiman's constant

$$
c_F =
\frac{2221564096 + 283748\sqrt{462}}{491993569}
= 4.52782956616087914088\ldots .
$$

However, Freiman's original proof relies on more than one hundred pages of intricate computation. The source is also difficult to access, and the argument has not been available in a form that can be independently and mechanically checked.

The goal of this repository is to build an automatic and rigorous algorithm for computing the left endpoint of Hall's ray, and to use it to either verify or refute Freiman's value.

## Mathematical Setup

For an irrational number $\alpha$, define its Lagrange constant by

$$
\ell(\alpha)
= \limsup_{q\to\infty}\frac{1}{q\|q\alpha\|},
$$

where $\|x\|$ denotes the distance from $x$ to the nearest integer. Equivalently, $\ell(\alpha)$ is the supremum of the real numbers $c$ for which

$$
\left|\alpha-\frac{p}{q}\right| < \frac{1}{cq^2}
$$

has infinitely many coprime integer solutions $p,q$. The Lagrange spectrum is

$$
L = \{\ell(\alpha): \alpha\in\mathbb{R}\setminus\mathbb{Q}\}.
$$

Perron's continued-fraction description gives

$$
L =
\left\{
\limsup_{n\to\infty}
\left(
[a_n; a_{n+1}, a_{n+2},\ldots]
+ [0; a_{n-1}, a_{n-2},\ldots]
\right)
: (a_n)_{n\in\mathbb{Z}}\in(\mathbb{N}^{*})^{\mathbb{Z}}
\right\}.
$$

This connects the problem to symbolic dynamics, continued fractions, and sums of Gauss-Cantor sets. In this project, interval containment statements in `L` will be reduced to rigorous finite computations about such symbolic and Cantor-set data.

## Freiman's Constant

The exact quadratic irrational form of Freiman's constant is

$$
c_F =
4 + \frac{253589820 + 283748\sqrt{462}}{491993569}
= \frac{2221564096 + 283748\sqrt{462}}{491993569}.
$$

For the algorithmic problem, the following continued-fraction decomposition is more useful than the simple continued fraction of `c_F` itself. Let

$$
P=(3,1,3,1,2,1).
$$

Then

$$
c_F =
[4;4,3,2,2,\overline{P}]
+ [0;3,2,1,1,\overline{P}],
$$

where the overline means periodic repetition. This form is directly adapted to Perron's formula: it describes the limiting local configuration that should realize the endpoint value.

The ordinary simple continued fraction of `c_F` is eventually periodic because `c_F` is quadratic irrational, but its period is very long. For this project, the periodic-tail decomposition above is the more relevant representation.

## Main Claim to Check

The central target is the statement

$$
[c_F,\infty) \subset L.
$$

Here $c_F$ is Freiman's constant.

If the verification succeeds, the repository should provide source code, certificates, and computation logs that make the proof independently checkable. If it fails, the project should help separate two possibilities: the algorithm is still too weak, or the traditional value of the endpoint is not correct.

## Planned Approach

The first milestone is to reproduce and extend accessible results close to Freiman's constant. In particular, Schecker proved

$$
[\sqrt{21},\infty) \subset L,
$$

where $\sqrt{21}=4.582\ldots$, which is relatively close to $c_F=4.527\ldots$.

The planned workflow is:

1. Implement basic tools for finite words, admissible words, forbidden words, and continued-fraction intervals.
2. Use rigorous interval arithmetic, or exact rational arithmetic where feasible, to avoid untracked floating-point error.
3. Search for constraints on words that imply interval containment for sums of Gauss-Cantor sets.
4. Combine these checks into an algorithm for proving statements of the form $[\alpha,\infty)\subset L$.
5. Push $\alpha$ as close as possible to Freiman's constant.
6. Produce proof certificates and computation logs that can be checked independently of the search program.
7. Formalize the certificate checker, or selected parts of the argument, in Lean if the computational proof becomes stable enough.

## Expected Repository Structure

Implementation has not started yet. The tentative structure is:

```text
.
├── src/              # Verification algorithms
├── tests/            # Unit tests and regression tests for known results
├── data/             # Search outputs, proof certificates, computation logs
├── lean/             # Lean formalization, if pursued
├── notes/            # Mathematical notes, literature notes, experiment logs
└── README.md
```

The implementation language, interval arithmetic backend, and Lean interface are still open design choices.

## Reproducibility Principles

This repository is not meant to contain only numerical experiments. The aim is to make every serious claim checkable by other researchers.

- Numerical computations should use interval arithmetic or exact arithmetic whenever correctness depends on rounding.
- Search results should be saved with enough data to reconstruct the proof.
- Failed searches and discarded constraints should be logged when they are mathematically informative.
- Known results, especially Schecker's $[\sqrt{21},\infty)\subset L$, should be used as regression tests.
- Final claims should be separated from the search code through small proof certificates.
- Any Lean formalization should focus first on checking certificates, keeping the trusted kernel of the computation small.

## Related Problems

An algorithm capable of verifying Freiman's constant may also be useful for other long-standing questions about the Lagrange and Markov spectra, including:

- Berstein's conjecture: $[4.1,4.52]\subset L$;
- whether `L` has interior points to the left of Hall's ray;
- the structure and dimension of `M \ L`, where `M` is the Markov spectrum;
- analogues of Hall's ray in dynamical Lagrange and Markov spectra.

## References

- G. A. Freiman, *Diophantine Approximation and the Geometry of Numbers (Markov's Problem)*, Kalinin State University Press, 1975. In Russian.
- M. Hall Jr., "On the sum and product of continued fractions", *Annals of Mathematics* 48 (1947), 966-993.
- T. W. Cusick and M. E. Flahive, *The Markoff and Lagrange Spectra*, Mathematical Surveys and Monographs 30, American Mathematical Society, 1989.
- H. Schecker, "Uber die Menge der Zahlen, die als Minima quadratischer Formen auftreten", *Journal of Number Theory* 9 (1977), 121-141.
- C. G. Moreira, "Geometric properties of the Markov and Lagrange spectra", *Annals of Mathematics* 188 (2018), 145-170. See also [arXiv:1612.05782](https://arxiv.org/abs/1612.05782).
- C. Matheus and C. G. Moreira, "Fractal geometry of the complement of Lagrange spectrum in Markov spectrum", *Commentarii Mathematici Helvetici* 95 (2020), 593-633. See also [arXiv:1803.01230](https://arxiv.org/abs/1803.01230).

Useful online references for the exact value of `c_F`:

- E. W. Weisstein, [Freiman's Constant](https://mathworld.wolfram.com/FreimansConstant.html), MathWorld.
- OEIS [A118472](https://oeis.org/A118472), decimal expansion of Freiman's constant.

## Current Status

This repository is at the project setup stage. It does not yet contain a verification of Freiman's constant.

## License

MIT License
