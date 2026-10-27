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

## Metadata: `*.meta.json`

Both `original.meta.json` and `table.meta.json` use the following fields.
Metadata records the generation settings and the meaning of the numeric input;
adopted-row membership is stored separately in `.alive.bin`. Array indices are
zero-based. Rational values are strings such as `"51/50"`, not floating-point
approximations.

### Generation settings

| Field | Meaning |
|---|---|
| `language` | Comma-separated forbidden-word setting: `31313` or `31313,13131` for the saved tables. |
| `forbidden` | The same forbidden words as arrays of digits. Appended tails use digits 1, 2, 3. |
| `memory` | Number of trailing digits retained in each state, currently 2. Forbidden-word matching information is retained separately. |
| `length` | Maximum total number of digits appended on the two sides by ordinary successor pairs, currently 3. |
| `spine` | Maximum length of extra candidates following an extremal tail up to their last digit, which may branch. It is 6 for `original` and 10 for `table`. |
| `return_length` | Length of optional extra candidates following an extremal tail exactly. Zero disables this addition. |
| `macro` | Optional Boolean, absent when disabled. For `original`, `true` adds pairs of rotations of the six-digit word `131213`. |
| `base` | Ratio-grid base, currently `51/50`. |
| `low`, `high` | Inclusive exponent range. Bin `k` represents `[base^k, base^(k+1)]`, giving `high-low+1` bins. |
| `grid` | Subdivision count for relative interval types, currently 32. |

`length` does not bound every word in `extensions`: `spine`, `return_length`,
and `macro` can add longer candidates. The finite candidate list is a search
choice, not a claim that all possible extensions have been enumerated.

### State and successor descriptions

| Field | Meaning |
|---|---|
| `keys` | One-sided state keys `[q, parity, suffix]`, in state-ID order. `q` is the length of the longest suffix matching a proper prefix of a forbidden word; `parity` is word length modulo 2; `suffix` contains the last `memory` digits. |
| `prototypes` | One concrete legal word for each key, in the same order. These represent states, not all concrete prefixes. |
| `extensions` | Candidate appended words, in extension-ID order. Entry 0 is `[]`, the empty word. Illegal extensions are rejected separately for each state. |
| `pairs` | Triples `[left_extension_id, right_extension_id, restricted]`. Flag 0 imposes no extremal-branch restriction; flag 1 requires both transitions to have `on_extremal_branch = 1` in the numeric input. |
| `bands` | Relative interval types, in type-ID order: `[0,1]`, followed by `[i/grid, (i+2)/grid]` for `i=0,...,grid-2`. |
| `radicand` | Square-root radicand used in exact endpoint arithmetic: 462 for `original`, 41667 for `table`. |
| `prehistory_interval` | Common enclosure `[1/4,4/5]` used beyond the retained reversed suffix when bounding continuant ratios. |

For example, key `[0,0,[1,2]]` represents an even-length word ending in `12`,
with no nonempty suffix matching a proper forbidden-word prefix. Storing only
two trailing digits therefore does not limit forbidden-word matching to two
digits.

For a restricted transition of length at most `spine`, all digits except the
last must follow the extremal tail attaining the parent's lower endpoint.
A transition of length `return_length`, when enabled, must follow that tail
exactly. Both sides must also be legal. Longer candidates do not automatically
preserve the ratio bin; this requires an exact derivative identity.

### Initial geometry and generation records

| Field | Meaning |
|---|---|
| `root_words` | Concrete left and right words used for the generator's initial geometry. |
| `root_scale` | Exact derivative ratio `abs(F_b'(xi_b))/abs(F_a'(xi_a))` for `root_words = [a,b]`, where `F_w` is the continued-fraction map and `xi_w` is the tail attaining its lower endpoint. Stored as four rational coefficients `[c0,0,c2,0]`, meaning `c0 + c2*sqrt(radicand)`. |
| `root_bin` | Exponent of the ratio bin containing `root_scale`. |
| `root` | Flattened initial geometry index, excluding interval type: `(left_state*S + right_state)*B + root_bin-low`, where `S=len(keys)` and `B=high-low+1`. |
| `transition_checks` | Number of legal one-sided state/extension transitions checked during generation. |
| `scope` | Description of the artifact's limits: exact geometry still requires closed-family and root checks. |

The metadata's `root_words` describes one generator root. The complete interval
verification uses the additional roots in `roots.json`, described below.
`verify.py` regenerates both `.dat` and `.meta.json` from the settings. It compares
numeric input byte for byte and metadata as JSON values, ignoring `scope` and
`transition_checks`. Extra metadata fields unused by the generator are ignored.
With `--independent`, `audit.py` also checks input semantics using the state and
word descriptions. Metadata alone does not certify closure or interval inclusion.

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
