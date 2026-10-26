# Preserved Berstein research tree

The earlier Berstein layout, experiments, interval verification,
and independent audits are preserved in [Berstein/](Berstein/README.md). The active shared
Lean project is now at [Lean/](../../Lean/README.md).
The current complete implementation is the six source files in
[the current interior-interval directory](../../markov_interior/README.md).

This snapshot preserves mathematical source and certificate bytes. The Lean
project has been promoted to the repository root, with its support scripts
adapted to that location. The three
adopted table files have moved to [markov_interior/certificates/](../../markov_interior/certificates/README.md);
relative links at their previous locations retain historical paths. The
snapshot's `.gitignore` explicitly retains the adoption-array link.

The sibling `Freiman/src/` freezes the original flat Python/C++ source dependencies
at the relative paths expected by the preserved code. Its `data/` preserves the original table and the small verification records
that refer to those frozen sources, independently of the active package's
updated import paths and verification records. The compact active interior-interval implementation does not
import this source snapshot.

## Run the old interval verification

From the repository root:

```sh
python3 -B -S archive/2026-10-26/Berstein/src/verify_interval_extensions.py --full
python3 -B -S archive/2026-10-26/Berstein/src/verify_lower_intervals.py
python3 -B -S archive/2026-10-26/Berstein/src/collect_exploration_results.py
```

Outputs from these historical commands are written under this snapshot's
`Berstein/data/`, `logs/`, and `bin/`. Recorded source/hash paths are interpreted
relative to this snapshot directory. The old documents describe the layout
within that historical context; their repository-root commands must be adjusted
to the snapshot path as above.

The complete current proof (both tables, root coverage and noncentral bounds),
including the independent coverage audits, runs without this snapshot:

```sh
python3 -B -S markov_interior/verify.py --independent
```

## Lean

Follow [the shared Lean guide](../../Lean/README.md), using `cd Lean` from the
repository root. The old snapshot path is a compatibility link. Theorem sources,
pinned dependencies, theorem scope, and the historical verification baseline are
unchanged; launcher paths were adapted to the shared location.
Builds and generated dependencies remain excluded from Git. Relocation does not
establish a new Lean result for the extended table.
