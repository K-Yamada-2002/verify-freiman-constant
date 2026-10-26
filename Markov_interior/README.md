# Interior intervals in the Markov spectrum

This directory contains the complete computer-assisted interval proof: finite
inputs, both closed tables, root coverage, all-position bounds, and the analytic
passage to infinite continued fractions. It runs on its own with Python's
standard library and a C++17 compiler. No archive or Freiman source tree is needed.

The verified rational intervals, strictly below Freiman's constant, are:

| Construction | Interval in both `M` and `L` |
|---|---|
| Original paper | `[4.52578, 4.52754]` |
| Extended component | `[4.52173315, 4.52762938]` |
| Lower interval | `[4.51104888, 4.52]` |

Their open intervals give interior points of `M`. These results do not establish
maximality or the whole conjectured `[4.1,4.52]` interval.

## Verify the complete proof

From the repository root:

```sh
python3 -B -S Markov_interior/verify.py --output /tmp/markov-interior-verified.json
```

Or copy this entire directory elsewhere and run `python3 -B -S verify.py` there.
The default command:

1. Regenerates the exact numeric input and metadata for **both** tables.
2. Independently checks input semantics and corruption controls.
3. Replays all **3,464,816 + 4,260,954 adopted rows**, holding membership fixed.
4. Checks all declared root bands, including the original paper's 25 bands.
5. Recomputes uniform bounds at every noncentral position and the bulk endpoints.
6. Checks exact interval coverage, rational inward rounding, gluing margins, and
   strict comparison with Freiman's constant for all three displayed claims.

The result includes `claims` and `interval_proof`, not just a table success flag.
The infinite arguments behind the finite obligations are proved in
**[PROOF.md](PROOF.md)**. This is a computer-assisted analytic proof; it does not
claim that new Lean theorems have been produced.

To repeat the entire table check with a separate C++ implementation too:

```sh
python3 -B -S Markov_interior/verify.py --independent
```

`--tables-only` deliberately stops before interval verification and emits no
interval claim. Builds and intermediate results use temporary directories.
Sources and certificates are hashed before and after the run. Python `-O` is
rejected because verification uses assertions.

## Read the implementation

| Source | Responsibility |
|---|---|
| [verify.py](verify.py) | The complete proof entry point |
| [proof.py](proof.py) | Concrete root membership, interval coverage, uniform noncentral bounds, periodic endpoints and the finite gluing obligations |
| [prepare.py](prepare.py) | Exact quadratic arithmetic, legal tails and finite geometry generation |
| [kernel.cpp](kernel.cpp) | Uniform successor covers: deletion search or fixed-table replay |
| [audit.py](audit.py) | Separately implemented input parser, algebra and input-semantics audit; used on every verification run |
| [audit.cpp](audit.cpp) | Optional separate all-row coverage verifier |

The dependency chain is `verify.py` → current code and
[certificates/](certificates/README.md). There are no local compatibility imports
or runtime references to historical implementations. See [FORMAT.md](FORMAT.md)
for row indexing and the two input universes.

## Search

```sh
python3 -B -S Markov_interior/prepare.py --output /tmp/markov-input
c++ -O3 -std=c++17 -pthread Markov_interior/kernel.cpp -o /tmp/markov-kernel
/tmp/markov-kernel /tmp/markov-input.dat /tmp/markov-search.json
```

This searches the extended table's default finite universe. The original
universe uses `--forbidden 31313 --macro --spine 6 --low -155 --high 154
--root 32113,4322`. See `prepare.py --help` for the other parameters.
Passing an adoption array as the kernel's third argument selects fixed-table
replay instead. A search stopped with `--round-limit` can be unfinished even
when rows remain; that is not a closed-family certificate.

## Documents and formal verification

The [paper PDF](../doc/paper.pdf) and [TeX source](../doc/paper.tex) in the root
`doc/` explain the shared successor-cover method, the Freiman ray, and the
original interior interval. [PROOF.md](PROOF.md) explains the two current languages and
extended claims, including the noncentral and gluing arguments.

The shared [Lean project](../Lean/README.md) remains at the repository root.
Its existing [interior-interval target](../Lean/Berstein/README.md) concerns the
original `31313` table and original Markov interval. It uses the unchanged
historical Freiman input, while this directory regenerates that membership
array's numeric geometry in the common format used by the current verifier.
The extended language and endpoints have not been added to that formalization.

Earlier experiments and superseded implementations are retained in Git history,
at commit `2ac2b5e20dedd8255954c5a32f5694649defd771`. They are not prerequisites
for this proof and are omitted from the current tree.
