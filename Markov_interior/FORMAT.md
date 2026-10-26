# Input and adoption array

`prepare.py` writes whitespace-separated integer text, not a list of concrete
continued fractions. `kernel.cpp` reads this format directly.

## Numeric input: `table.dat`

The extended input `certificates/table.dat` starts with:

```text
FREIMAN_DYADIC_GRAPH_V1 26 244 -140 140 32 6927 7691
```

| Field | Meaning |
|---|---|
| `26` | One-sided states: forbidden-word state, parity, and suffix |
| `244` | Candidate one-sided extension words, including the empty word |
| `-140 140` | Ratio-box exponents; 281 boxes with base `51/50` |
| `32` | Interval types |
| `6927` | Allowed pairs of extension-word indices, with restriction flags |
| `7691` | Initial geometry index, without interval type |

Following the header are the interval types, extension pairs, ratio boundaries,
and the one-sided endpoint/transition data. Endpoint bounds are integer
numerators with denominator `2^48`; IDs and flags are plain integers. The
record definitions follow below.

`certificates/table.meta.json` records the state labels, extension words, interval types, and
generator parameters. Neither file enumerates all continued-fraction prefixes.
Each abstract row covers a whole parameter box and infinitely many prefixes.
Successor candidates are finite and bounded by the generator settings.

## Adoption array: `table.alive.bin`

C++ expands the candidate row product:

```text
26 left states × 26 right states × 281 ratio boxes × 32 types
= 6,078,592 rows
```

The adoption array has exactly that many bytes, with no header or bit packing:
`0x00` means absent; `0x01` means adopted. The extended saved array has 4,260,954 ones.
For zero-based state/type IDs and an exponent `i` from -140 to 140:

```python
index = (((left * 26 + right) * 281 + (i + 140)) * 32 + interval_type)
adopted = data[index] == 1
```

No chosen successor menu is stored per row. The kernel reconstructs the covers
from the candidate input and adopted destinations. Passing the array to the
kernel requests fixed-family verification. Omitting it requests deletion search.
Kernel output `result.json` is accompanied by `result.json.alive.bin` in the
same byte format; the fixed certificate uses the shorter name `table.alive.bin`.

## Original language and roots

`certificates/original.dat` has header:

```text
FREIMAN_DYADIC_GRAPH_V1 22 91 -155 154 32 1824 89736
```

Its adoption array has `22 * 22 * 310 * 32 = 4,801,280` bytes, with
3,464,816 ones. Use `S=22`, `B=310`, `T=32`, and `L=-155` in the general
index formula `(((left*S+right)*B+(exponent-L))*T+interval_type)`. The
extended universe uses `S=26`, `B=281`, `T=32`, and `L=-140`.

`certificates/roots.json` adds the initial conditions needed for interval
inclusion. Each row contains `a`, `b`, `center`, `band`, `geometry`, `bin`,
and `types`. `proof.py` computes the exact continuant ratios and derivative
ratio, verifies the stated geometry and ratio box, checks every adopted type,
and requires their union to cover the whole declared band. It then derives
the endpoints and all-position bound from the words. Table membership alone
is not an interval proof.

## Complete numeric record layout

After the header `FREIMAN_DYADIC_GRAPH_V1 S E L H T P root`, let
`B = H-L+1`. The whitespace-separated records are:

1. `T` pairs: relative lower and upper endpoints of each interval type.
2. `P` triples `(u, w, restricted)`: extension indices and a restriction flag.
3. `B+1` pairs: outward enclosures of the ratio-grid boundaries.
4. For each of the `S` one-sided states:
   - a pair enclosing its normalized full width;
   - `(parity, r_lower, r_upper, anchor_id, endpoint_count)`;
   - one enclosing pair for each distinct tail endpoint;
   - one record for each of the `E` extension words. An illegal extension is
     just `-1`. A legal record is
     `(child, on_extremal_branch, constant_tag, scale_lower, scale_upper,
     eta0_lower, eta0_upper, eta1_lower, eta1_upper, endpoint0_id, endpoint1_id)`.

All interval bounds are integer numerators over `2^48`. IDs, counts, and flags
are ordinary integers. `audit.py` parses this format and independently checks
its exact meanings against the words in the metadata. Shared tail IDs support
exact cancellation in endpoint comparisons; equal constant tags are checked
by exact derivative identities.
