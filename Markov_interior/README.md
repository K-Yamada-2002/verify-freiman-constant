# Markov interior input generation

[prepare.py](prepare.py) generates V2 numeric input and matching JSON metadata.
Run it with SageMath's Python from the repository root:

```sh
sage -python -B Markov_interior/prepare.py --output /tmp/markov-v2
```

The output files are `/tmp/markov-v2.dat` and `/tmp/markov-v2.meta.json`.
The default language forbids `31313` and `13131`. Use `--lower-tail-depth`
to set the maximum length of candidates following the minimizing tail.
The source comments describe each section and include complete small examples.

V2 omits the V1 header's `root` and the two fixed eta intervals in each
transition. Metadata uses `lower_tail_depth` and omits the old root and
return-length settings. [verify.py](verify.py) orchestrates regeneration,
table replay, and the interval proof. Its new `kernel.cpp` and `proof.py`
dependencies are the next components to implement.

## Original verifier

[old/](old/) contains the complete original code, documentation, and proof
certificates, preserved without edits. Its V1 verifier runs with:

```sh
sage -python -B Markov_interior/old/verify.py --output /tmp/markov-v1-verified.json
```

Run its regression suite with:

```sh
sage -python -B -m unittest discover -s Markov_interior/old -p 'test_*.py' -v
```

The original [proof](old/PROOF.md), [format guide](old/FORMAT.md), and
[README](old/README.md) are included in that snapshot.
