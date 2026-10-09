# Standalone English paper

`markov_interior.tex` isolates the completed 31313-avoiding Markov-interval construction from `generalized_t.tex`. It includes the continued-fraction and automaton definitions, closed-cover realization argument, finite-certificate obligations, root calculation, full noncentral-bound argument matching `SpectralVerified.lean`, main proof, formal theorem mapping, trust boundary, and reproduction commands. It makes no claim about the unfinished 131-forbidden problem or inclusion in the Lagrange spectrum.

Build from the repository root with an ordinary pdfLaTeX installation:

```sh
mkdir -p /tmp/markov-paper-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/markov-paper-build Berstein/doc/markov_interior.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/markov-paper-build Berstein/doc/markov_interior.tex
```

The exposition was checked against source snapshot `4b38497822c2088f9103a3c31aa4a1ac9a2a1462` and the committed execution baseline. During manuscript preparation, both `independent_input.py` and `independent_spectral.py` were rerun successfully. All 4,372 rational spectral checks displayed in the paper were also replayed using a separate Python `Fraction` implementation. The 10-page PDF compiled with resolved references and no overfull boxes and was rendered for layout inspection.

The 3,464,816-row exhaustive replay and complete Lean proof build were **not rerun during manuscript preparation**. Their historical successful results are documented in `../Lean/verification-baseline.json`; the paper distinguishes those records from kernel verification of the conditional soundness theorem. The immutable release remains unchanged.
