# Proof architecture

The chosen method proves the soundness of an executable finite checker in
Lean and runs that checker on the original fixed table. Reducing acceptance
of the concrete large table inside the kernel is not a completion criterion
for this method.

## Dependencies

```text
Finite words, the 31313-avoidance automaton, bounds on infinite continued fractions
  ↓
Exact quadratic-field endpoint IDs, state transitions, and constant tags
  ↓
Sound rational interval arithmetic, shape/derivative ratios, endpoint differences
  ↓
Coverage of all adopted rows, all destinations, and ratio boxes
  ↓
Extensions of actual finite prefixes and preservation of invariants
  ↓
Nested nonempty compact cylinders, shrinking on both sides, realized points
  ↓
25 root bands → interval filling by sums of actual continued fractions

Finite checks near the core + six-digit/automaton bounds for distant positions
  ↓
4,372 kernel checks → bound at every noncentral position

Interval filling + uniform noncentral bound + exact radical comparisons
  ↓
Maximum attained at the center → membership in the Markov spectrum
  ↓
[4.52578,4.52754] ⊂ M ∩ (-∞,c_F) → interior in the real topology
```

## Conditions connecting the mathematics

- Endpoint identity requires exact equality in the quadratic field; a shared outer enclosure is insufficient.
- Constant multiplier tags require exact cross-product identities and equality of values.
- Child coverage paths check both endpoints and every link, covering every adopted band.
- A child's ratio must lie in a verified box, including boundary cases.
- Successor states carry actual left/right prefixes and shape/ratio invariants, not just row numbers.
- Growth of prefix continuants and bounded multiplier ratios imply shrinking cylinders on both sides.
- The noncentral bound quantifies over every legal tail and every nonzero integer position.

## Final verification

`python3 scripts/verify.py --prepare` performs the following checks:

1. Compare hashes of the original input and cited source files.
2. Build the mathematical proofs through `Main` and the executable checker.
3. Audit the final theorem statements and their axioms.
4. Generate witnesses and confirm acceptance of all 484 state pairs and 3,464,816 rows.
5. Confirm rejection of six kinds of corrupted input.
6. Save a record linking inputs, executable, sources, witnesses, and execution logs.

`--reuse-replay` reuses a saved exhaustive acceptance run only after checking
all relevant hashes and the ranges and counts in the logs. The mathematical
proof build, axiom audit, and corruption tests run each time. Consult
`logs/verification.json` for the latest completed run and
[verification-baseline.json](verification-baseline.json) for the committed baseline.
