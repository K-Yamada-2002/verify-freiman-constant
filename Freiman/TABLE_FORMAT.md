# Finite-table input and adoption format

The implementation is [prepare.py](prepare.py)
on the writer side and [kernel.cpp](kernel.cpp) on the
reader side. The following describes the current `graph_wide` graph format.

## What is enumerated

A candidate row is `(left_state, right_state, ratio_box, interval_type)`.
A one-sided state records the forbidden-word automaton state, length parity,
and a suffix. It represents infinitely many concrete prefixes; this is not an
enumeration of all continued-fraction words.

For `graph_wide`, there are 22 one-sided states, 310 ratio boxes and 32 interval
types. C++ expands the product `22 * 22 * 310 * 32 = 4,801,280` candidate rows.
Each row is a condition over an entire parameter box, rather than a numerical
sample. Successor words are a fixed finite selection, not all possible words.

## `.dat`: numeric input, not the adoption table

The file is whitespace-separated text. Its header is:

```text
FREIMAN_DYADIC_GRAPH_V1 S E L H T P root
```

The current header is:

```text
FREIMAN_DYADIC_GRAPH_V1 22 91 -155 154 32 1824 89736
```

| Field | Meaning |
|---|---|
| `S` | Number of one-sided states |
| `E` | Number of one-sided extension words, including the empty word |
| `L`, `H` | First and last ratio-box exponents; `B = H - L + 1` |
| `T` | Number of interval types |
| `P` | Number of extension-pair candidates |
| `root` | Flattened initial geometry index, without the interval-type index |

The remaining records appear in this order:

1. `T` pairs of integers: the relative endpoints of the interval types.
2. `P` triples `(u_index, w_index, restricted)`: extension-word indices and a
   flag restricting the pair to extremal-branch candidates.
3. `B + 1` pairs: outward enclosures of the ratio-grid boundaries.
4. For each of the `S` one-sided states:
   - one pair enclosing the normalized full width;
   - `(parity, r_lower, r_upper, anchor_endpoint_id, endpoint_count)`;
   - one enclosing pair for each distinct tail endpoint;
   - one record for each of the `E` extension words. An illegal transition is
     the single integer `-1`. Otherwise the record contains
     `(child_state, on_extremal_branch, constant_tag, scale_lower, scale_upper,
     eta0_lower, eta0_upper, eta1_lower, eta1_upper, endpoint0_id, endpoint1_id)`.

Numeric endpoint and bound integers are interpreted with denominator `2^48`;
indices, flags and counts are ordinary integers. For example, the interval-type
record `0 17592186044416` means `[0, 1/16]`. Numeric bounds are rounded outward;
the C++ checker uses integer interval arithmetic.

The companion `.meta.json` supplies human-readable state signatures, extension
words, type names, the grid base `51/50`, and the other generator parameters.
The `.dat` factors out shared one-sided data instead of writing millions of
fully expanded row records.

## `.alive.bin`: adopted rows

This is a headerless byte array, with one byte per candidate row:

- `0x00`: row is not adopted.
- `0x01`: row is adopted.

There is no bit packing. The last index changes fastest:

```python
index = (((left * S + right) * B + (exponent - L)) * T + interval_type)
adopted = data[index] == 1
```

State and type IDs are zero-based and follow the ordering in the metadata.
For `graph_wide`, the file is 4,801,280 bytes, with 3,464,816 ones and
1,336,464 zeros. The file contains membership decisions; it does not store
the chosen successor cover for every row. The C++ checker reconstructs covers
from the candidates and adopted destinations.

## Search versus verification

Without an adoption file, `kernel.cpp` starts with every candidate row
adopted and repeatedly deletes rows that cannot be covered using remaining
rows. With an adoption file, it fixes the supplied rows and rejects a failed
cover instead of repairing the table through deletion.

The historical seed-expansion search is preserved at
`../archive/2026-10-27/Freiman/search/graph_kernel_expand.cpp`. Protected seed rows must still pass
the ordinary fixed-table checker afterward. Search bounds and selected
candidates limit what the search can discover; empty output does not prove
that no mathematical successor cover exists.
