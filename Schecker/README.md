# Schecker

Notebooks implementing and extending the interval method of Schecker (1977).

## Notebooks

- `schecker_proof_1.ipynb` searches for admissible bilateral continued-fraction
  intervals and the corresponding portions of the Lagrange spectrum.
- `schecker_proof_2.ipynb` investigates Schecker's Lemma 2 and the auxiliary
  formulae used in its proof.
- `schecker_proof_3.ipynb` searches directly for short admissible
  3-successors that cover a given T-interval.

## `schecker_proof_3.ipynb`

The third notebook is a numerical discovery tool for the successor statement
in Lemma 1. It deliberately does not use the fixed lists in Lemma 2 or the
formula in Hilfssatz 4.

Given

```math
A=(a_{-1},\ldots,a_{-h}\mid a_1,\ldots,a_k),
```

the notebook enumerates proper successors

```math
I(Au\mid Aw), \qquad u,w\in\{1,2,3\}^*,
```

in increasing order of `len(u) + len(w)`. For every candidate, it computes the
T-interval and T-ratio directly from their definitions and checks all three
admissibility conditions. The admissible candidates are then passed to the
standard greedy algorithm for covering a one-dimensional interval. For a
fixed candidate family, this produces a cover with the minimum number of
intervals.

The principal single-input function is:

```python
result = search_short_admissible_successors(
    A=([3], [2]),
    max_total_length=4,
)
show_search_result(result)
```

For `A = ([3], [2])`, the search finds at successor depth two the cover

```math
I(\mathord{\sim}\mid\mathord{\sim}1)
\mathbin{\cup} I(\mathord{\sim}\mid\mathord{\sim}2)
\mathbin{\cup} I(\mathord{\sim}2\mid\mathord{\sim}3).
```

This gives a replacement for the invalid list from Lemma 2 for this particular
input, but it is not by itself a proof of the universal statement in Lemma 1.

### Exhaustive finite surveys

The notebook can also enumerate every base interval up to a specified total
depth. Here the depth of `A` is `h + k`, while `successor_depth` is the separate
cutoff `len(u) + len(w)` for the successors tested for each `A`.

```python
exhaustive_result = run_exhaustive_A_survey(
    A_depth=3,
    successor_depth=4,
    progress_every=50,
)
exhaustive_summary_table(exhaustive_result)
```

Before admissibility filtering, the number of inputs of exact depth `d` is
`(d - 1) * 4^d`, since both sides of `A` must be nonempty. The survey:

1. enumerates all such base words with `2 <= h + k <= A_depth`;
2. retains the admissible T-intervals;
3. searches for a short admissible 3-successor cover of each interval;
4. groups the results by the parity of `h + k` and by successor-cover type.

By default, a cover type and its left-right reflection are assigned the same
canonical type. Set `identify_reflections=False` to retain the two
orientations separately.

The summary table has the following columns:

- `parity`: the parity of `h + k`;
- `covered`: whether a cover was found within `successor_depth`;
- `count`: the number of enumerated admissible inputs in the group;
- `min nu(A)`, `max nu(A)`: the smallest and largest observed T-ratios in the
  finite group;
- `successor depth`: the range of first successful successor depths among the
  covered members; for a `NOT COVERED` row, this displays the tested cutoff;
- `canonical successor-cover type`: one greedy cover, written in geometric
  left-to-right order and identified with its reflection by default;
- `examples`: representative base intervals belonging to the group.

`NOT COVERED` means only that no cover was found within the specified
successor-depth cutoff. It is not evidence that no admissible successor cover
exists. Likewise, the displayed T-ratio bounds are the extrema of a finite
sample, not a certified continuous range. A cover type need not be unique:
the table records the minimum-cardinality cover selected by the deterministic
greedy search at the first successful depth.

### Numerical status

The notebook currently uses 160-bit real arithmetic. Its output is intended
to discover plausible replacement lists and exceptional cases. Any list used
in a proof must subsequently be certified with exact algebraic arithmetic or
rigorous interval arithmetic.
