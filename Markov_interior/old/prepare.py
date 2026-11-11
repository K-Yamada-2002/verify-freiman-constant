"""Build the exact input geometry for the finite successor-cover checker.

Read generate_input first, then the three geometric formulas immediately
below it. The remaining sections explain legal tails, candidate selection,
and the integer records consumed by kernel.cpp. SageMath handles arithmetic.

A word is a tuple of digits, such as (1, 2). Its continued-fraction map is
F_word(t) = [0; word_1, ..., word_n + t], with F_empty(t) = t. Infinite appended
tails use digits 1, 2, 3 and avoid the selected forbidden words. Fixed root
prefixes may also contain 4.

This program writes .dat and .meta.json. It chooses a finite candidate
universe; it does not choose the adopted rows or prove that they form a
closed family. Those tasks belong to kernel.cpp and verify.py.
"""
import argparse
import json
from fractions import Fraction
from functools import lru_cache
from itertools import product
from pathlib import Path

from sage.all import AA, QQ, ZZ, QuadraticField

DENOMINATOR = 1 << 48  # Common denominator for numeric input bounds.

# Successor-pair flags in the C++ input format. A restricted pair is usable
# only when both one-sided transitions are eligible for the extremal branch.
UNRESTRICTED = 0
REQUIRE_BRANCH = 1

# select_language changes these together and clears language-dependent caches.
FORBIDDEN_WORDS = ((3, 1, 3),)
FORBIDDEN_PREFIXES = ((), (3,), (3, 1))
RADICAND = 5
FIELD = QuadraticField(RADICAND, 'r', embedding=AA(RADICAND).sqrt())


def generate_input(args):
    """Assemble the candidate universe, locate its root, and write both files.

    With the default settings there are 26 left states, 26 right states,
    281 derivative-ratio bins, and 32 relative interval types. These describe
    26*26*281*32 candidate rows implicitly; we do not serialize each row here.
    """
    select_language(args.forbidden)
    memory, grid = args.memory, args.grid
    assert memory >= 2 and grid > 1 and grid & (grid - 1) == 0

    # State IDs follow sorted keys. Representatives retain their discovery
    # order, which also determines the order of some extension-word IDs.
    representatives = representative_prefixes(memory)
    state_keys = sorted(representatives)
    state_ids = {key: i for i, key in enumerate(state_keys)}
    extension_words, extension_pairs = candidate_extensions(args, representatives)
    relative_bands = relative_interval_types(grid)

    # S is the right/left derivative ratio at the two lower-endpoint tails.
    # Bin k represents base**k <= S <= base**(k+1), including both boundaries.
    ratio_base = parse_rational(args.base)
    first_exponent, last_exponent = args.low, args.high
    bin_count = last_exponent - first_exponent + 1
    root_words = tuple(tuple(map(int, text)) for text in args.root.split(','))
    root_scale = root_derivative_ratio(*root_words)
    # next chooses the first matching bin if S lies exactly on a shared cut.
    root_exponent = next(
        exponent for exponent in range(first_exponent, last_exponent + 1)
        if ratio_base**exponent <= root_scale <= ratio_base**(exponent + 1))

    left_state_id, right_state_id = (
        state_ids[prefix_state_key(word, memory)] for word in root_words)
    state_pair_id = left_state_id * len(state_keys) + right_state_id
    root_index = state_pair_id * bin_count + (root_exponent - first_exponent)
    # Default example: IDs (1,1) give pair 27, and exponent -36 has offset
    # 104 from -140. The flattened root index is 27*281 + 104 = 7691.

    # Each state block records the exact geometry and all legal transitions.
    state_records, transition_count = encode_state_records(
        args, representatives, state_ids, extension_words)

    # A representative labels a parameter box; its own finite continuant
    # ratio need not lie in that box. The concrete root ratios must lie in it.
    for word, continuant_ratio in zip(root_words, continuant_parameters(*root_words)[:2]):
        lower, upper = continuant_bounds(word, memory)
        assert lower <= continuant_ratio <= upper

    # Keep the established key order as well as the values: metadata files
    # must reproduce byte for byte. Tuples become JSON arrays automatically.
    metadata = {
        # Generation settings.
        'language': args.forbidden,
        'forbidden': FORBIDDEN_WORDS,
        'radicand': RADICAND,
        'memory': memory,
        'length': args.length,
        'spine': args.spine,
        'grid': grid,
        'return_length': args.return_length,
        'base': str(ratio_base),
        'low': first_exponent,
        'high': last_exponent,
        # Labels in the numeric-ID order used by .dat.
        'keys': state_keys,
        'prototypes': [representatives[key] for key in state_keys],
        'extensions': extension_words,
        'pairs': extension_pairs,
        'bands': [[str(lower), str(upper)] for lower, upper in relative_bands],
        # The generator's chosen root; roots.json supplies further proof roots.
        'root_words': root_words,
        'root': root_index,
        'root_bin': root_exponent,
        'root_scale': serialize_quadratic(root_scale),
        'transition_checks': transition_count,
        'prehistory_interval': ['1/4', '4/5'],
        'scope': 'Exact geometry only; a closed family and root check are required.',
    }
    if args.macro:
        metadata['macro'] = True
    write_input_files(args.output, metadata, state_records)

    summary = {
        'sides': len(state_keys),
        'extensions': len(extension_words),
        'pairs': len(extension_pairs),
        'rows': len(state_keys)**2 * bin_count * len(relative_bands),
        'checks': transition_count,
    }
    print(json.dumps(summary), flush=True)


# Geometric core for F_word: r is the reversed continuant ratio q_(n-1)/q_n.


def normalized_width_bounds(prefix, r_bounds):
    """Bound cylinder width in units of the lower-endpoint derivative.

    Let x0 and x1 be the tails mapping to the lower and upper endpoints of
    the parent cylinder. For a prefix of length n, the normalized width is

        (-1)**n * (x1-x0) * (1+r*x0) / (1+r*x1).

    This follows by dividing F_prefix(x1)-F_prefix(x0) by |F_prefix'(x0)|.
    Here r varies over a whole state box; it is not replaced by the finite
    representative's own continuant ratio. The expression is monotone in r,
    so evaluating the two box endpoints gives its exact range.
    """
    anchor, opposite = oriented_tail_endpoints(prefix)
    return sorted((-1)**len(prefix) * (opposite - anchor) * (1 + r * anchor)
                  / (1 + r * opposite) for r in r_bounds)


def derivative_scale_bounds(prefix, extension, r_bounds):
    """Bound the child-to-parent derivative scale throughout a state box.

    If F_extension(t) = (a*t+b)/(c*t+d), composition with F_prefix gives

        |F_(prefix+extension)'(child_anchor)| / |F_prefix'(anchor)|
          = ((1+r*anchor) / ((c+r*a)*child_anchor+d+r*b))**2.

    Both anchors are tails attaining the corresponding lower endpoints.
    The ratio before squaring is positive and monotone in r. Thus these
    two endpoint evaluations certify every r in the box, not a sample.
    An empty extension gives the constant scale [1,1].
    """
    anchor = oriented_tail_endpoints(prefix)[0]
    child_anchor = oriented_tail_endpoints(prefix + extension)[0]
    a, b, c, d = cf_matrix(extension)
    # The positive ratio is monotone in r, so both endpoints suffice.
    ratios = [(1 + r * anchor) / ((c + r * a) * child_anchor + d + r * b)
              for r in r_bounds]
    return sorted(ratio * ratio for ratio in ratios)


def root_derivative_ratio(left_word, right_word):
    """Compute the root coordinate S = |F_right'| / |F_left'| exactly.

    Unlike the two functions above, this uses concrete root prefixes, so
    r_left and r_right are exact values rather than intervals. The factors
    q_left**2/q_right**2 and the anchor correction come from
    |F_word'(t)| = 1 / (q_word * (1+r_word*t))**2.
    """
    left_r, right_r, denominator_ratio = continuant_parameters(left_word, right_word)
    anchor_ratio = ((1 + left_r * oriented_tail_endpoints(left_word)[0])
                    / (1 + right_r * oriented_tail_endpoints(right_word)[0]))
    return denominator_ratio * anchor_ratio * anchor_ratio


# Legal tails and their finite state representation.


def select_language(forbidden):
    """Select forbidden words, matching states, and the exact quadratic field.

    For example, '31313,13131' means that neither five-digit word may occur
    in an appended tail. A matching state is a proper forbidden-word prefix
    that also occurs as a suffix of the word read so far.

    The supported extremal tails lie in Q(sqrt(5)), Q(sqrt(462)), or
    Q(sqrt(41667)). The positive real embedding fixes the meaning of < and >.
    Process one language at a time: matching and tail caches use this active
    language. Matrix products depend only on their digits and need no reset.
    """
    global FORBIDDEN_WORDS, FORBIDDEN_PREFIXES, RADICAND, FIELD
    FORBIDDEN_WORDS = tuple(tuple(map(int, word)) for word in forbidden.split(','))
    fields = {
        ((3, 1, 3),): 5,
        ((3, 1, 3, 1, 3),): 462,
        ((3, 1, 3, 1, 3), (1, 3, 1, 3, 1)): 41667,
    }
    assert FORBIDDEN_WORDS in fields, 'Unsupported exact extremal field'
    RADICAND = fields[FORBIDDEN_WORDS]
    FORBIDDEN_PREFIXES = tuple(sorted({word[:i] for word in FORBIDDEN_WORDS
                                      for i in range(len(word))}))
    FIELD = QuadraticField(RADICAND, 'r', embedding=AA(RADICAND).sqrt())
    # These cached tails depend on the active language.
    suffix_state.cache_clear()
    extremal_tail_cycle.cache_clear()
    extremal_tail_value.cache_clear()
    return FIELD


def next_suffix_state(state, digit):
    """Update the forbidden-word matcher after one digit.

    Only a newly completed suffix can become forbidden. With forbidden word
    31313, state (3,1,3,1) followed by 3 is rejected; followed by 2 it resets
    to (). An empty tuple is a valid state, whereas None means rejection.
    """
    word = state + (digit,)
    if any(word[-len(bad):] == bad for bad in FORBIDDEN_WORDS):
        return None
    return max((s for s in FORBIDDEN_PREFIXES if not s or word[-len(s):] == s), key=len)


@lru_cache(None)
def suffix_state(word):
    """Return the final matching suffix, or None if the word is illegal.

    After select_language('31313,13131'):
        suffix_state((1,2))       == ()
        suffix_state((1,2,1))     == (1,)
        suffix_state((3,1,3,1,3)) is None

    Callers must test 'is not None', since () represents a legal word too.
    """
    state = ()
    for digit in word:
        state = next_suffix_state(state, digit)
        if state is None:
            return None
    return state


@lru_cache(None)
def cf_matrix(word):
    """Return (a,b,c,d) for F_word(t) = (a*t+b)/(c*t+d).

    A digit contributes the matrix [[0,1],[1,digit]]. Multiplying in word
    order composes the maps t -> 1/(digit+t). For example:

        cf_matrix(())     == (1,0,0,1)   # identity map
        cf_matrix((1,2))  == (1,2,1,3)   # F_(1,2)(t) = (t+2)/(t+3)

    The determinant is (-1)**len(word), explaining the alternating order
    used in tail selection. The reversed continuant ratio is r = c/d.
    """
    a, b, c, d = 1, 0, 0, 1
    for digit in word:
        a, b, c, d = b, a + digit * b, d, c + digit * d
    return a, b, c, d


def evaluate_cf(word, x):
    """Evaluate F_word at a Sage rational or quadratic tail value.

    For example, evaluate_cf((1,2), QQ(0)) == QQ((2,3)). Using Sage input
    values keeps division exact when running this .py file without a preparser.
    """
    a, b, c, d = cf_matrix(word)
    return (a * x + b) / (c * x + d)


@lru_cache(None)
def extremal_tail_cycle(state, minimum):
    """Return (preperiod, period) for a minimizing or maximizing legal tail.

    Continued-fraction order reverses at each digit. A minimum therefore
    takes the largest legal digit at odd positions and the smallest at even
    positions. Every legal choice extends infinitely by 2s, since none of
    these forbidden words contains 2; no backtracking is needed.

    The pair (matching state, position parity) has finitely many values.
    Its first repetition identifies the periodic part. In the default
    language, extremal_tail_cycle((), True) returns
    ((), (3,1,3,1,2,1,3,1,3,2)), representing [0; overline(3131213132)].
    """
    seen = {}
    digits = ()
    odd = True
    while (state, odd) not in seen:
        seen[state, odd] = len(digits)
        choices = [d for d in (1, 2, 3) if next_suffix_state(state, d) is not None]
        # Continued-fraction order alternates. Every choice extends by infinitely many 2s.
        digit = max(choices) if minimum == odd else min(choices)
        digits += (digit,)
        state, odd = next_suffix_state(state, digit), not odd
    start = seen[state, odd]
    return digits[:start], digits[start:]


@lru_cache(None)
def extremal_tail_value(state, minimum):
    """Turn an eventually periodic extremal tail into an exact field element."""
    preperiod, period = extremal_tail_cycle(state, minimum)
    return evaluate_cf(preperiod, periodic_tail_value(period, FIELD))


def periodic_tail_value(period, field):
    """Evaluate [0; overline(period)] in a field containing its square root.

    For nonempty period with matrix (a,b,c,d), its value solves
    c*x**2 + (d-a)*x - b = 0. We choose the positive fixed point in (0,1).
    For example, period (1,) in Q(sqrt(5)) gives (sqrt(5)-1)/2.
    """
    a, b, c, d = cf_matrix(period)
    discriminant = (d - a)**2 + 4 * c * b
    x = (a - d + abs(field(discriminant).sqrt())) / (2 * c)
    assert evaluate_cf(period, x) == x and 0 < x < 1
    return x


def oriented_tail_endpoints(prefix, extension=()):
    """Return tails attaining the lower and upper images under F_prefix.

    Values are in the input coordinate of F_prefix: after extending by u,
    they have the form F_u(extremal tail). They are not yet the endpoints
    of the full continued-fraction cylinder.

    For an odd-length prefix F_prefix decreases, so the first returned tail
    is numerically larger. In all cases the order guarantees
    F_prefix(first) <= F_prefix(second). This orientation defines the anchor
    used to normalize widths and derivatives throughout the checker.
    """
    state = suffix_state(prefix + extension)
    assert state is not None
    low, high = sorted(evaluate_cf(extension, extremal_tail_value(state, t))
                       for t in (True, False))
    return (low, high) if len(prefix) % 2 == 0 else (high, low)


def cylinder_hull(prefix):
    """Return the actual lower and upper cylinder endpoints after applying F_prefix."""
    return tuple(sorted(evaluate_cf(prefix, extremal_tail_value(suffix_state(prefix), t))
                        for t in (True, False)))


def continuant_parameters(left_word, right_word):
    """Return concrete (r_left, r_right, q_left**2/q_right**2).

    The last row of a prefix matrix is (previous denominator, denominator).
    For example, words (1,2) and (2,) give (1/3, 1/2, 9/4).
    """
    _, _, left_previous_q, left_q = cf_matrix(left_word)
    _, _, right_previous_q, right_q = cf_matrix(right_word)
    return (QQ((left_previous_q, left_q)),
            QQ((right_previous_q, right_q)),
            QQ((left_q**2, right_q**2)))


def continuant_bounds(prefix, memory):
    """Build the state's allowed interval for the reversed continuant ratio r.

    Reverse the retained suffix and append a prehistory parameter in
    [1/4,4/5]. This interval is invariant under t -> 1/(digit+t) for digits
    1,2,3. Include the whole matched forbidden prefix if it exceeds memory.

    For suffix (1,2) and memory 2 the resulting box is [5/14,9/23]. It is a
    parameter box for the state, not a bound on every short representative:
    the finite word (1,2) itself has r=1/3, outside this box. Concrete roots
    are checked separately, and each transition must preserve its child box.
    """
    length = max(memory, len(suffix_state(prefix)))
    return tuple(sorted(evaluate_cf(prefix[-length:][::-1], t)
                        for t in (QQ((1, 4)), QQ((4, 5)))))


def prefix_state_key(word, memory):
    """Label a legal prefix by (matched-prefix length, parity, retained suffix).

    In the default language, (1,2) gives (0,0,(1,2)); appending 1 gives
    (1,1,(2,1)). The key omits the full word and the exact continuant ratio:
    infinitely many longer prefixes can share it.
    """
    matched_length = len(suffix_state(word))
    parity = len(word) % 2
    retained_suffix = word[-memory:]
    return matched_length, parity, retained_suffix


def lower_tail_prefix(word, length):
    """Take length digits of the tail attaining the lower endpoint of F_word.

    Odd prefix length exchanges the numerical minimum and maximum tail.
    Repeating the period length+1 times supplies enough digits for any
    requested finite length, including length=0.
    """
    preperiod, period = extremal_tail_cycle(suffix_state(word), len(word) % 2 == 0)
    return (preperiod + period * (length + 1))[:length]


# Finite candidate choices and numeric encoding.


def representative_prefixes(memory):
    """Choose the first legal word encountered for each abstract state key.

    Enumerate by increasing length and then lexicographic digit order.
    Lengths through max(memory+1, longest forbidden word) cover the contexts
    used by these languages, including both word-length parities.

    These words label states; they are not a list of all prefixes to verify.
    Preserve discovery order: candidate_extensions visits representatives in
    this order when assigning extension IDs. State IDs are sorted separately.
    """
    representatives = {}
    longest_forbidden_word = max(map(len, FORBIDDEN_WORDS))
    max_length = max(memory + 1, longest_forbidden_word)
    for length in range(memory, max_length + 1):
        for word in product((1, 2, 3), repeat=length):
            if suffix_state(word) is not None:
                key = prefix_state_key(word, memory)
                representatives.setdefault(key, word)
    return representatives


def relative_interval_types(grid):
    """List relative subintervals of a parent hull, in interval-type ID order.

    Type 0 is the whole [0,1]. The remaining types have width 2/grid and
    overlap their neighbors by 1/grid. For grid=4 the complete list is
    [(0,1), (0,1/2), (1/4,3/4), (1/2,1)]. With grid=32 there are 32 types.

    If a parent hull is [L,H] and W=H-L, a relative band [p,q] denotes
    [L+p*W, L+q*W]. These bands define candidate row types, not adoption bits.
    """
    bands = [(QQ(0), QQ(1))]
    for offset in range(grid - 1):
        lower = QQ((offset, grid))
        upper = QQ((offset + 2, grid))
        bands.append((lower, upper))
    return bands


def candidate_extensions(args, representatives):
    """Build a finite menu of extension words and left/right extension pairs.

    Each pair is (left_extension_id, right_extension_id, restriction_flag).
    Ordinary pairs append at least one digit and at most args.length digits
    in total. Further candidates follow extremal branches, with optional
    periodic macros and longer exact returns. Their legality and destination
    state depend on the parent and are checked later in encode_state_records.

    Candidate selection is a bounded search choice. Completeness of this
    menu is not assumed; kernel.cpp must prove the required successor covers.
    """
    extension_words = [word for length in range(args.length + 1)
                       for word in product((1, 2, 3), repeat=length)]
    extension_ids = {word: i for i, word in enumerate(extension_words)}

    def register_extension(word):
        # Assign a new ID only on first occurrence. Never sort this list:
        # changing an ID would change both numeric input and metadata.
        if word not in extension_ids:
            extension_ids[word] = len(extension_words)
            extension_words.append(word)
        return extension_ids[word]

    # IDs 0,1 denote (), (1,): pair (0,1,0) appends 1 only on the right.
    extension_pairs = {(i, j, UNRESTRICTED) for i, u in enumerate(extension_words)
                       for j, v in enumerate(extension_words)
                       if 0 < len(u) + len(v) <= args.length}

    # The original construction also tries all pairs of rotations of this
    # six-digit period. These candidates have no extremal-branch restriction.
    if args.macro:
        assert args.forbidden == '31313'
        period = (1, 3, 1, 2, 1, 3)
        rotations = [period[i:] + period[:i] for i in range(len(period))]
        rotation_ids = [register_extension(word) for word in rotations]
        extension_pairs |= {(left, right, UNRESTRICTED)
                            for left in rotation_ids for right in rotation_ids}

    # Follow each lower-endpoint tail for k digits, then try every last digit.
    # The last digit may branch away from the extremal tail. For example,
    # branch (3,1,3,...) contributes (3,1,1), (3,1,2), (3,1,3) at length 3.
    for word in representatives.values():
        extremal_branch = lower_tail_prefix(word, args.spine)
        for length in range(args.spine):
            for digit in (1, 2, 3):
                extension = extremal_branch[:length] + (digit,)
                register_extension(extension)

    # Equal-length branch pairs are usable only when each parent's own
    # transition has its branch-eligibility flag set. Already unrestricted
    # pairs need no second copy with this restriction.
    unrestricted = {(i, j) for i, j, _ in extension_pairs}
    extension_pairs |= {(i, j, REQUIRE_BRANCH) for i, u in enumerate(extension_words)
                        for j, v in enumerate(extension_words)
                        if 0 < len(u) == len(v) <= args.spine and (i, j) not in unrestricted}

    # An optional longer return must follow the extremal tail exactly.
    # Whether paired returns preserve a ratio bin is decided by exact equal
    # derivative tags, not by their word lengths or a floating-point guess.
    if args.return_length:
        return_ids = set()
        for word in representatives.values():
            extension = lower_tail_prefix(word, args.return_length)
            return_ids.add(register_extension(extension))
        extension_pairs |= {(left, right, REQUIRE_BRANCH)
                            for left in return_ids for right in return_ids}
    return extension_words, sorted(extension_pairs)


def label_tail_endpoints(prefix, extension_words):
    """Assign local IDs to exact endpoints in first-appearance order.

    For example, [x0,x1,x2,x1] receives IDs [0,1,2,1]. Equality is tested
    in the exact quadratic field, before numerical rounding. Overlapping
    rounded enclosures alone do not justify assigning a common ID.

    These IDs are local to one parent state. Shared IDs allow kernel.cpp
    to cancel equal endpoint terms exactly when comparing interval ends.
    """
    endpoint_ids = {}
    for extension in extension_words:
        if suffix_state(prefix + extension) is None:
            continue
        for endpoint in oriented_tail_endpoints(prefix, extension):
            if endpoint not in endpoint_ids:
                endpoint_ids[endpoint] = len(endpoint_ids)
    return endpoint_ids


def encode_state_records(args, representatives, state_ids, extension_words):
    """Compute and serialize each parent state's geometry and transitions.

    A state block has: one width interval; its parity, r interval and anchor;
    one interval per endpoint ID; and one record per extension-word ID.
    An illegal extension contributes just '-1'. All others contribute a
    transition record, including the empty extension back to the same state.
    """
    lines = []
    # This registry spans all parent states. Equal positive IDs certify the
    # same exact, r-independent derivative scale; 0 means no constant tag.
    constant_scale_ids = {}
    transition_count = 0
    for key in state_ids:
        prefix = representatives[key]
        parent_r_bounds = continuant_bounds(prefix, args.memory)
        anchor_tail = oriented_tail_endpoints(prefix)[0]

        # Compute the full-box geometry before converting to dyadic integers.
        width = normalized_width_bounds(prefix, parent_r_bounds)
        lines.append(f'{outward_numerators(width[0])[0]} {outward_numerators(width[1])[1]}')

        endpoint_ids = label_tail_endpoints(prefix, extension_words)
        state_header = [
            len(prefix) % 2,
            outward_numerators(parent_r_bounds[0])[0],
            outward_numerators(parent_r_bounds[1])[1],
            endpoint_ids[anchor_tail],
            len(endpoint_ids),
        ]
        lines.append(' '.join(map(str, state_header)))
        lines += [' '.join(map(str, outward_numerators(x))) for x in endpoint_ids]

        extremal_branch = lower_tail_prefix(prefix, args.spine)
        return_word = lower_tail_prefix(prefix, args.return_length) if args.return_length else ()
        for extension in extension_words:
            extended_word = prefix + extension
            if suffix_state(extended_word) is None:
                lines.append('-1')
                continue
            child_state_key = prefix_state_key(extended_word, args.memory)
            child_state_id = state_ids[child_state_key]
            assert suffix_state(representatives[child_state_key]) == suffix_state(extended_word)

            # Appending u transforms the reversed ratio as r -> F_reverse(u)(r).
            # Its entire image must fit the representative child's parameter box.
            child_r_image = tuple(sorted(evaluate_cf(extension[::-1], r) for r in parent_r_bounds))
            child_r_bounds = continuant_bounds(representatives[child_state_key], args.memory)
            assert child_r_bounds[0] <= child_r_image[0] <= child_r_image[1] <= child_r_bounds[1]

            derivative_bounds = derivative_scale_bounds(prefix, extension, parent_r_bounds)
            constant_scale_id = 0
            if derivative_bounds[0] == derivative_bounds[1]:
                if derivative_bounds[0] not in constant_scale_ids:
                    constant_scale_ids[derivative_bounds[0]] = len(constant_scale_ids) + 1
                constant_scale_id = constant_scale_ids[derivative_bounds[0]]

            # A restricted branch candidate may deviate only at its last digit.
            # At the optional return length, require the exact return word instead.
            branch_eligible = (
                bool(extension) and len(extension) <= args.spine
                and extension[:-1] == extremal_branch[:len(extension) - 1])
            if args.return_length and len(extension) == args.return_length:
                branch_eligible = extension == return_word

            child_endpoint_ids = tuple(
                endpoint_ids[x] for x in oriented_tail_endpoints(prefix, extension))
            lines.append(encode_transition(
                child_state_id=child_state_id,
                branch_eligible=branch_eligible,
                constant_scale_id=constant_scale_id,
                derivative_bounds=derivative_bounds,
                endpoint_ids=child_endpoint_ids,
            ))
            transition_count += 1
    return lines, transition_count


def encode_transition(*, child_state_id, branch_eligible, constant_scale_id,
                      derivative_bounds, endpoint_ids):
    """Pack one legal transition in the established C++ record format.

    Fields are: child ID, branch flag, constant-scale tag, two derivative
    bounds, two legacy eta intervals, and two parent-local endpoint IDs.
    Both eta intervals remain [0,1] for file-format compatibility.

    Writing D for 2**48, default parent state 0 and extension (1,) give
    '11 1 0 scale_lo scale_hi 0 D 0 D 2 1'. Thus the child is state 11,
    its scale varies with r, and its endpoints use parent-local IDs 2 and 1.
    """
    lower_scale = outward_numerators(derivative_bounds[0])[0]
    upper_scale = outward_numerators(derivative_bounds[1])[1]
    record = [
        child_state_id,
        int(branch_eligible),
        constant_scale_id,
        lower_scale,
        upper_scale,
        0, DENOMINATOR,  # eta0 = [0,1]
        0, DENOMINATOR,  # eta1 = [0,1]
        *endpoint_ids,
    ]
    return ' '.join(map(str, record))


def write_input_files(output, metadata, state_records):
    """Write integer text for C++ and matching human-readable JSON labels.

    The .dat layout is: header, relative bands, successor pairs, ratio-grid
    cuts, then the per-state blocks. Interval bounds are integer numerators
    over DENOMINATOR; counts, IDs and flags are ordinary unscaled integers.

    The default header is:
        FREIMAN_DYADIC_GRAPH_V1 26 244 -140 140 32 6927 7691
    The first band line is '0 281474976710656', meaning [0,1]. See FORMAT.md
    for the complete field definitions. This function makes no search choices.
    """
    state_count = len(metadata['keys'])
    extension_count = len(metadata['extensions'])
    band_count = len(metadata['bands'])
    pair_count = len(metadata['pairs'])
    first_exponent, last_exponent = metadata['low'], metadata['high']
    header = [
        'FREIMAN_DYADIC_GRAPH_V1',
        state_count,
        extension_count,
        first_exponent,
        last_exponent,
        band_count,
        pair_count,
        metadata['root'],
    ]
    lines = [' '.join(map(str, header))]

    # Saved grids have exactly representable dyadic band endpoints.
    for lower, upper in metadata['bands']:
        lower_numerator = int(parse_rational(lower) * DENOMINATOR)
        upper_numerator = int(parse_rational(upper) * DENOMINATOR)
        lines.append(f'{lower_numerator} {upper_numerator}')
    lines += [' '.join(map(str, pair)) for pair in metadata['pairs']]

    # B bins need B+1 cuts: base**low through base**(high+1).
    ratio_base = parse_rational(metadata['base'])
    for exponent in range(first_exponent, last_exponent + 2):
        cut_bounds = outward_numerators(ratio_base**exponent)
        lines.append(' '.join(map(str, cut_bounds)))
    lines += state_records

    # One output prefix gives two files, e.g. /tmp/table.dat and
    # /tmp/table.meta.json. No adoption array (.alive.bin) is written here.
    path = Path(output).expanduser().resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.with_suffix('.dat').write_text('\n'.join(lines) + '\n')
    path.with_suffix('.meta.json').write_text(json.dumps(metadata, indent=2) + '\n')


# Preserve the certificate encoding while Sage handles arithmetic and rounding.


def parse_rational(text):
    """Read fraction or decimal text exactly, including on SageMath 10.2.

    Both '51/50' and '1.02' give QQ((51,50)). Fraction is used only to parse
    the text: unlike conversion through float, this preserves every decimal
    digit. All subsequent arithmetic uses Sage's rational or quadratic field.
    """
    return QQ(Fraction(text).as_integer_ratio())


def outward_numerators(x):
    """Enclose x by integer numerators over the fixed denominator 2**48.

    Write x = a+b*sqrt(d). If m=floor(10**60*sqrt(d)), then sqrt(d) lies
    between m/10**60 and (m+1)/10**60. Multiply this rational enclosure by b,
    reverse its order when b is negative, add a, and round the two bounds
    outward to denominator 2**48.

    For example, 1/16 gives (17592186044416,17592186044416). The returned
    integers are numerators, not the rational endpoints themselves.

    The decimal enclosure precision is part of the saved-data convention.
    Directly rounding exact x could give a narrower interval under severe
    cancellation, changing certificate bytes despite remaining mathematically
    valid. Retain the established enclosure before applying Sage floor/ceil.
    """
    rational_part, radical_coefficient = FIELD(x).list()
    root_denominator = 10**60
    root_floor = ZZ(RADICAND * root_denominator**2).isqrt()
    root_lower = QQ((root_floor, root_denominator))
    root_upper = QQ((root_floor + 1, root_denominator))
    radical_lower, radical_upper = sorted((
        radical_coefficient * root_lower,
        radical_coefficient * root_upper,
    ))
    lower_numerator = (DENOMINATOR * (rational_part + radical_lower)).floor()
    upper_numerator = (DENOMINATOR * (rational_part + radical_upper)).ceil()
    return int(lower_numerator), int(upper_numerator)


def serialize_quadratic(value):
    """Encode a field element as [rational, 0, radical, 0] strings.

    For example, 2+sqrt(d)/3 becomes ['2','0','1/3','0']. The two zero slots
    retain the existing certificate format; they are not extra field terms.
    Keeping rational coefficients as strings avoids decimal approximations.
    """
    rational_part, radical_coefficient = value.list()
    return [str(rational_part), '0', str(radical_coefficient), '0']


def main():
    if not __debug__:
        raise RuntimeError('Verification requires Python assertions; do not use -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'out/Markov_interior/table',
                        help='Output prefix for .dat and .meta.json files')
    parser.add_argument('--memory', type=int, default=2,
                        help='Trailing digits retained in an abstract prefix state')
    parser.add_argument('--length', type=int, default=3,
                        help='Maximum total appended digits in an ordinary successor pair')
    parser.add_argument('--spine', type=int, default=10,
                        help='Maximum length of candidates branching from an extremal tail')
    parser.add_argument('--grid', type=int, default=32,
                        help='Power-of-two subdivision count for relative interval types')
    parser.add_argument('--base', default='51/50',
                        help='Derivative-ratio grid base as an exact fraction or decimal')
    parser.add_argument('--low', type=int, default=-140,
                        help='First ratio-bin exponent, inclusive')
    parser.add_argument('--high', type=int, default=140,
                        help='Last ratio-bin exponent, inclusive')
    parser.add_argument('--root', default='112222,122222',
                        help='Comma-separated outward prefixes for the left and right root')
    parser.add_argument('--forbidden', choices=('313', '31313', '31313,13131'),
                        default='31313,13131', help='Forbidden words in appended tails')
    parser.add_argument('--macro', action='store_true',
                        help='Include the original six-digit periodic successor pairs')
    parser.add_argument('--return-length', type=int, default=0,
                        help='Length of optional exact extremal returns; 0 disables them')
    args = parser.parse_args()
    if args.length < 1 or args.spine < 0 or args.return_length < 0 or args.low >= args.high:
        parser.error('Require length >= 1, spine/return-length >= 0, and low < high')
    generate_input(args)


if __name__ == '__main__':
    main()
