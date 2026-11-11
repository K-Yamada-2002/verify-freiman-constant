"""Write exact geometry input and JSON labels. Run with SageMath's Python."""
import argparse
from contextlib import ExitStack
from fractions import Fraction
from functools import cache
from io import StringIO
from itertools import product
import json
from math import ceil, floor
from pathlib import Path

DENOMINATOR = 1 << 48
DIGITS = '123'
UNRESTRICTED = 0
REQUIRE_BRANCH = 1


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'out/Markov_interior/table_2',
                        help='Output prefix for .dat and .meta.json files')
    parser.add_argument('--forbidden', choices=('313', '31313', '31313,13131'),
                        default='31313,13131', help='Forbidden words in continued-fraction tails')
    parser.add_argument('--memory', type=int, default=2,
                        help='Trailing digits retained in each state')
    parser.add_argument('--length', type=int, default=3,
                        help='Maximum total extension length in ordinary pairs')
    parser.add_argument('--lower-tail-depth', type=int, default=10,
                        help='Maximum extension length per side along the minimizing tail')
    parser.add_argument('--macro', action='store_true',
                        help='Include the original six-digit periodic extension pairs')
    parser.add_argument('--grid', type=int, default=32,
                        help='Power-of-two subdivision count for relative intervals')
    parser.add_argument('--base', default='51/50',
                        help='Derivative-ratio grid base as a fraction or decimal')
    parser.add_argument('--low', type=int, default=-140,
                        help='First ratio-bin exponent, inclusive')
    parser.add_argument('--high', type=int, default=140,
                        help='Last ratio-bin exponent, inclusive')
    args = parser.parse_args()
    if args.grid < 2 or DENOMINATOR % args.grid != 0:
        parser.error('--grid must be a power of two from 2 through 2^48')
    if args.memory < 2 or args.length < 1 or args.lower_tail_depth < 0:
        parser.error('Require --memory >= 2, --length >= 1, and --lower-tail-depth >= 0')
    if args.macro and args.forbidden != '31313':
        parser.error('--macro requires --forbidden 31313')
    try:
        args.base = Fraction(args.base)
    except (ValueError, ZeroDivisionError):
        parser.error('--base must be a fraction or decimal')
    if args.base <= 1:
        parser.error('--base must be greater than 1')
    if args.low > args.high:
        parser.error('--low must be at most --high')
    return args


def prefix_state_key(word, memory, forbidden_words):
    """Return (matched-prefix length, parity, retained suffix) for a legal word.

    With the default language and memory=2, '12' gives (0, 0, '12'),
    and appending '1' gives (1, 1, '21').
    """
    proper_prefixes = {bad[:i] for bad in forbidden_words for i in range(1, len(bad))}
    matched = max((len(p) for p in proper_prefixes if word.endswith(p)), default=0)
    return matched, len(word) % 2, word[-memory:]


def representative_prefixes(memory, forbidden_words):
    """Return a dict mapping each state key to a representative digit string.

    The key is (match_length, parity, suffix). Match length counts the
    longest suffix that matches the start of a forbidden word. Parity is
    0 for even lengths and 1 for odd. Suffix stores the last memory digits.

    For memory=2 and forbidden words 31313 and 13131, the result includes

        {(0, 0, '22'): '22', (4, 0, '31'): '3131'}

    Both '22' and '1122' share the first key. Words are visited by length,
    then lexicographically, so '22' is kept. Extension IDs depend on this
    discovery order.
    """
    max_length = max(memory + 1, max(map(len, forbidden_words)))
    representatives = {}
    for length in range(memory, max_length + 1):
        for digits in product(DIGITS, repeat=length):
            word = ''.join(digits)
            if any(bad in word for bad in forbidden_words):
                continue
            state = prefix_state_key(word, memory, forbidden_words)
            representatives.setdefault(state, word)
    return representatives


def extremal_tail_cycle(word, forbidden_words, *, lower):
    """Return (preperiod, period) of the tail attaining the chosen endpoint.

    For the lower endpoint, start with the largest legal digit after an
    even-length word and the smallest after an odd-length word. Reverse
    that choice for the upper endpoint. Alternate thereafter because each
    map x -> 1/(digit + x) reverses order. Any legal choice can continue
    with 2s. Repeating the suffix and digit order starts a cycle.
    """
    context_length = max(map(len, forbidden_words)) - 1
    suffix = word[-context_length:]
    prefer_largest = lower if len(word) % 2 == 0 else not lower
    digits = []
    seen = {}
    while (suffix, prefer_largest) not in seen:
        seen[suffix, prefer_largest] = len(digits)
        digit_order = DIGITS[::-1] if prefer_largest else DIGITS
        digit = next(d for d in digit_order if not (suffix + d).endswith(forbidden_words))
        digits.append(digit)
        suffix = (suffix + digit)[-context_length:]
        prefer_largest = not prefer_largest
    start = seen[suffix, prefer_largest]
    return ''.join(digits[:start]), ''.join(digits[start:])


def lower_tail_prefix(word, length, forbidden_words):
    """Return the first length digits of the tail giving the lower endpoint."""
    preperiod, period = extremal_tail_cycle(word, forbidden_words, lower=True)
    return (preperiod + period * (length // len(period) + 1))[:length]


def candidate_extensions(args, representatives, forbidden_words):
    """Return (words, pairs), the extensions and combinations to try.

    The inputs are the CLI settings, the state-to-word dict from
    representative_prefixes(), and a tuple of forbidden digit strings.

    A pair (left_id, right_id, flag) tells the checker to append
    words[left_id] to the current left word and words[right_id] to the
    current right word. An empty string appends zero digits. The flag
    controls where the pair can be tried.

    Flag 0 makes the pair a candidate wherever both appends are legal.
    Flag 1 adds a test on each side. Take the infinite continuation of
    the current word that gives the smallest continued-fraction value.
    The digits being appended must match that continuation through the
    next-to-last digit of the extension. For example, after '22' the
    minimizing continuation starts with '31312' in the default language.
    Appending '312' passes the branch test because its first two digits
    are '31'.

    With --length 2, --lower-tail-depth 0, and --macro disabled, the first
    list is

        ['', '1', '2', '3', '11', '12', '13', '21', '22', '23', '31', '32', '33']

    The second list contains 33 pairs. For example, (0, 4, 0) appends '11'
    on the right only, and (1, 2, 0) appends '1' on the left and '2' on
    the right. Both pairs append two digits in total.

    Register ordinary words first, by length and then lexicographically.
    Their pairs append 1 through --length digits in total. Next register
    optional macro rotations and then branch words.
    --lower-tail-depth sets the maximum length of the extra branch words.
    For a tail starting with '313' and depth 3, the length-three choices
    are '311', '312', and '313'. A value of 0 skips these additions. Pair
    words of equal length up to this depth, unless the pair is already
    unrestricted.
    """
    word_ids = {}

    def register(word):
        return word_ids.setdefault(word, len(word_ids))

    for length in range(args.length + 1):
        for digits in product(DIGITS, repeat=length):
            register(''.join(digits))
    pairs = {(i, j, UNRESTRICTED) for (u, i), (v, j) in product(word_ids.items(), repeat=2)
             if 0 < len(u) + len(v) <= args.length}

    if args.macro:
        period = '131213'
        rotation_ids = [register(period[i:] + period[:i]) for i in range(len(period))]
        pairs.update((i, j, UNRESTRICTED) for i, j in product(rotation_ids, repeat=2))

    for word in representatives.values():
        tail = lower_tail_prefix(word, args.lower_tail_depth, forbidden_words)
        for offset in range(args.lower_tail_depth):
            for digit in DIGITS:
                register(tail[:offset] + digit)

    unrestricted = {(i, j) for i, j, _ in pairs}
    pairs.update((i, j, REQUIRE_BRANCH) for (u, i), (v, j) in product(word_ids.items(), repeat=2)
                 if 0 < len(u) == len(v) <= args.lower_tail_depth and (i, j) not in unrestricted)

    return list(word_ids), sorted(pairs)


def write_header(output, args, *, state_count, extension_count, pair_count):
    """Write one ASCII header line to the open .dat file.

    The fields appear in this order, followed by a newline.

        FREIMAN_DYADIC_GRAPH_V2 S E L H T P

    S counts the prefix states available on either side.
    E counts the extension words, including the empty word.
    L and H are the first and last ratio-bin exponents, from --low and
    --high. Both are inclusive. Bin k runs from base**k to base**(k+1).
    T counts the relative interval types and comes directly from --grid.
    P counts the candidate pairs of left and right extension words.
    """
    header = (
        'FREIMAN_DYADIC_GRAPH_V2',
        state_count,
        extension_count,
        args.low,
        args.high,
        args.grid,
        pair_count,
    )
    output.write(' '.join(map(str, header)) + '\n')


def write_relative_intervals(output, grid):
    """Write grid relative intervals immediately after the header.

    Type 0 is [0, 1]. Then write [i/grid, (i+2)/grid] for i from 0 through
    grid-2, in increasing order. Adjacent intervals in this second group
    overlap by 1/grid. For grid=4 the types are [0, 1], [0, 1/2],
    [1/4, 3/4], and [1/2, 1].

    In a parent interval [a, b], a relative interval [p, q] selects
    [a + p*(b-a), a + q*(b-a)]. Each line stores the two numerators over
    DENOMINATOR, separated by one space. Grid divides DENOMINATOR, so the
    numerators are exact integers.
    """
    step = DENOMINATOR // grid
    output.write(f'0 {DENOMINATOR}\n')
    for offset in range(grid - 1):
        lower = offset * step
        upper = (offset + 2) * step
        output.write(f'{lower} {upper}\n')


def write_extension_pairs(output, pairs):
    """Write one line per pair, after the relative intervals.

    Each line has the left extension ID, right extension ID, and flag,
    separated by spaces. IDs are zero-based positions in the shared word
    list. For example, '0 1 0' appends nothing on the left and the digit 1
    on the right. Flag 0 imposes no branch condition. Flag 1 requires both
    one-sided transitions to be eligible for the extremal branch.
    """
    for left, right, flag in pairs:
        output.write(f'{left} {right} {flag}\n')


def write_ratio_cuts(output, base, low, high):
    """Write the boundaries of the derivative-ratio bins after the pairs.

    Bin k is [base**k, base**(k+1)] for k from low through high. Write
    high-low+2 lines, one per boundary from base**low to base**(high+1).
    For base=3/2, low=-1, and high=0, the cuts are 2/3, 1, and 3/2.

    Each line encloses one boundary using two numerators over 2**48.
    Multiply the exact rational boundary by DENOMINATOR, then take its
    floor and ceiling. The two numerators coincide for an exact cut.
    """
    for exponent in range(low, high + 2):
        scaled = DENOMINATOR * base**exponent
        output.write(f'{floor(scaled)} {ceil(scaled)}\n')


@cache
def periodic_tail_value(preperiod, period):
    """Evaluate [0; preperiod, repeating period] as an exact algebraic real."""
    from sage.all import AA, continued_fraction

    initial = (0, *map(int, preperiod))
    repeating = tuple(map(int, period))
    return AA(continued_fraction((initial, repeating)).value())


def tail_endpoints(word, extension, forbidden_words):
    """Return the extended interval's two endpoints in the parent's tail coordinate.

    Find the lower and upper endpoint tails after word+extension, then
    apply the extension's continued-fraction map. Applying F_word to the
    returned pair gives the actual lower and upper endpoints, in that order.
    For word='12' and extension='1', the returned values are approximately
    (0.5584814274, 0.7905698397) in the default language.
    """
    endpoints = []
    for lower in (True, False):
        preperiod, period = extremal_tail_cycle(word + extension, forbidden_words, lower=lower)
        value = periodic_tail_value(preperiod, period)
        for digit in reversed(extension):
            value = 1 / (int(digit) + value)
        endpoints.append(value)
    return tuple(endpoints)


def state_r_bounds(state, word):
    """Return the state's exact rational interval for r = q_previous/q.

    Keep the last memory digits of word, or the whole matched forbidden
    prefix if it is longer. Apply the reversed suffix's continued-fraction
    map to z in [1/4, 4/5] to get the r interval. For suffix '12' this is
    r = (1+z)/(3+2*z), giving [5/14, 9/23].
    """
    from sage.all import QQ

    match_length, _, suffix = state
    retained = word[-max(len(suffix), match_length):]
    lower, upper = QQ((1, 4)), QQ((4, 5))
    for digit in map(int, retained):
        lower, upper = 1 / (digit + upper), 1 / (digit + lower)
    return lower, upper


def state_geometry(state, word, extension_words, forbidden_words):
    """Return width, r bounds, parity, anchor ID, and the exact endpoint-to-ID dict.

    Obtain the r interval from state_r_bounds().
    Let xi and omega be the tails giving the lower and upper endpoints.
    Dividing the full width by |F_word'(xi)| gives
    (-1)**parity * (omega-xi) * (1+r*xi) / (1+r*omega).
    This is monotone in r, so evaluating the two ends gives its range.

    Visit legal extensions in ID order, taking the lower endpoint first.
    Assign each distinct exact tail value its first-appearance ID, before
    rounding. For [xi, omega, x2, omega], the IDs are [0, 1, 2, 1].
    With default settings, state (0, 0, '12') has 302 endpoints, anchor
    ID 0, and r bounds (5/14, 9/23). Extension '1' uses IDs (2, 1).
    """
    _, parity, _ = state
    r_lower, r_upper = state_r_bounds(state, word)
    xi, omega = tail_endpoints(word, '', forbidden_words)
    widths = [(-1)**parity * (omega - xi) * (1 + r * xi) / (1 + r * omega)
              for r in (r_lower, r_upper)]

    endpoint_ids = {}
    for extension in extension_words:
        if any(bad in word + extension for bad in forbidden_words):
            continue
        for endpoint in tail_endpoints(word, extension, forbidden_words):
            endpoint_ids.setdefault(endpoint, len(endpoint_ids))

    return {
        'width_bounds': (min(widths), max(widths)),
        'parity': parity,
        'r_bounds': (r_lower, r_upper),
        'anchor_id': endpoint_ids[xi],
        'endpoints': endpoint_ids,
    }


def derivative_scale_bounds(word, extension, r_bounds, forbidden_words):
    """Bound |F_(word+extension)'(eta)| / |F_word'(xi)| over the whole r interval.

    Xi and eta are the tails giving the parent and child lower endpoints.
    Use the usual continued-fraction matrix [[p_h, p_(h-1)], [q_h, q_(h-1)]].
    Thus a=p_h, b=p_(h-1), c=q_h, d=q_(h-1), and F_extension(t)=(a+b*t)/(c+d*t).
    For extension '12', (a, b, c, d)=(2, 1, 3, 1).
    Composition gives the scale ((1+r*xi) / ((d+r*b)*eta+c+r*a))**2.
    Its positive ratio is monotone in r, so the interval endpoints give
    exact extrema.

    For default state 0 and extension '1', the scale ranges from about
    0.255688 to 0.259591. Following the minimizing tail exactly preserves
    the lower endpoint and gives a constant scale, such as xi**2 for '3'.
    """
    # Start with (p_0, p_(-1), q_0, q_(-1)) for the empty extension.
    a, b, c, d = 0, 1, 1, 0
    for digit in map(int, extension):
        a, b, c, d = digit * a + b, a, digit * c + d, c
    xi = tail_endpoints(word, '', forbidden_words)[0]
    eta = tail_endpoints(word + extension, '', forbidden_words)[0]
    scales = [((1 + r * xi) / ((d + r * b) * eta + c + r * a))**2
              for r in r_bounds]
    return min(scales), max(scales)


def write_state_data(output, representatives, extension_words, forbidden_words, lower_tail_depth):
    """Compute and write each state's geometry, in sorted state-key order.

    Take one representative word, compute its geometry, then write its block.
    The first line stores the width's lower and upper numerators.
    The second line stores parity, lower and upper r numerators, anchor
    ID, and endpoint count. Bounds are rounded outward over 2**48.
    Then write one lower/upper numerator pair per distinct endpoint.
    The endpoint ID is its zero-based row number within this list.
    IDs follow first appearance in the candidate words. For example,
    the empty extension uses IDs (0, 1), and extension '1' uses (2, 1)
    in the first state. The shared upper endpoint appears once in the list.

    Finish the block with one transition row per extension word, in ID order.
    An illegal extension writes '-1'. A legal row contains seven integers

        child_id tail_flag constant_tag scale_lower scale_upper endpoint0 endpoint1

    Tail flag 1 requires a nonempty extension of at most lower_tail_depth
    digits, matching the minimizing tail through its next-to-last digit.
    Equal positive constant tags certify exactly equal, r-independent scales
    across all parent states. Scale bounds are numerators over 2**48, and
    the two endpoint IDs refer to this parent's endpoint list.
    With --length 1 and --lower-tail-depth 0 in the default language,
    state 0 has six endpoints and four extensions. Its complete block is

        124905066861958 126493390753360
        0 100526777396662 110142382191127 0 6
        74290155475950 74290155475951
        222525627220369 222525627220370
        157198546780128 157198546780129
        100866487089948 100866487089949
        124330156573740 124330156573741
        86238011931456 86238011931457
        0 0 1 281474976710656 281474976710656 0 1
        11 0 0 71969748764786 73068384612800 2 1
        4 0 0 33841015631187 34016662693599 3 4
        12 0 2 19607523429388 19607523429389 0 5

    Lines 1 and 2 are width and state information. Lines 3 through 8 are
    endpoints 0 through 5. Lines 9 through 12 are transitions for '', '1',
    '2', and '3'. All tail flags are 0 because the configured depth is 0.
    The next state's width line follows immediately after this block.
    """
    state_ids = {key: i for i, key in enumerate(sorted(representatives))}
    constant_scale_ids = {}
    for state_key, word in sorted(representatives.items()):
        state = state_geometry(state_key, word, extension_words, forbidden_words)
        lower, upper = state['width_bounds']
        width_lower = (DENOMINATOR * lower).floor()
        width_upper = (DENOMINATOR * upper).ceil()
        # 1. Append the normalized-width lower and upper numerators over 2**48.
        # State 0 in the small example above writes
        #   124905066861958 126493390753360
        output.write(f'{width_lower} {width_upper}\n')

        r_lower, r_upper = state['r_bounds']
        state_header = (
            state['parity'],
            (DENOMINATOR * r_lower).floor(),
            (DENOMINATOR * r_upper).ceil(),
            state['anchor_id'],
            len(state['endpoints']),
        )
        # 2. Append parity, r lower/upper numerators, anchor ID, and endpoint count.
        # State 0 in the small example writes
        #   0 100526777396662 110142382191127 0 6
        output.write(' '.join(map(str, state_header)) + '\n')

        # 3. Append one lower/upper numerator pair per endpoint, in ID order.
        # State 0 in the small example writes all six endpoint rows below.
        #   74290155475950 74290155475951
        #   222525627220369 222525627220370
        #   157198546780128 157198546780129
        #   100866487089948 100866487089949
        #   124330156573740 124330156573741
        #   86238011931456 86238011931457
        for endpoint in state['endpoints']:
            lower = (DENOMINATOR * endpoint).floor()
            upper = (DENOMINATOR * endpoint).ceil()
            output.write(f'{lower} {upper}\n')

        # 4. Append one transition row per extension, including the empty word.
        # State 0 in the small example writes all four rows for '', '1', '2', '3'.
        #   0 0 1 281474976710656 281474976710656 0 1
        #   11 0 0 71969748764786 73068384612800 2 1
        #   4 0 0 33841015631187 34016662693599 3 4
        #   12 0 2 19607523429388 19607523429389 0 5
        minimizing_tail = lower_tail_prefix(word, lower_tail_depth, forbidden_words)
        for extension in extension_words:
            extended_word = word + extension
            # Default state 0 rejects '313231313', which contains '31313'.
            if any(bad in extended_word for bad in forbidden_words):
                output.write('-1\n')
                continue

            # Appending '1' to state (0, 0, '12') gives (1, 1, '21'), ID 11.
            memory = len(state_key[2])
            child_key = prefix_state_key(extended_word, memory, forbidden_words)
            child_id = state_ids[child_key]

            # Appending digit d maps r to 1/(d+r). Check the whole parent's
            # interval maps inside the child's interval before using this edge.
            image_lower, image_upper = state['r_bounds']
            for digit in map(int, extension):
                image_lower, image_upper = 1 / (digit + image_upper), 1 / (digit + image_lower)
            child_lower, child_upper = state_r_bounds(child_key, representatives[child_key])
            if not child_lower <= image_lower <= image_upper <= child_upper:
                raise ValueError(f'Child r interval is not preserved by {word!r} + {extension!r}')

            # Evaluate the derivative scale at both r endpoints. A constant
            # gets one global tag, reused wherever the exact same value occurs.
            # The empty extension has scale 1, receives tag 1, and reuses it.
            # Default state 0 with extension '3' has scale xi**2 and gets tag 2.
            scale_lower, scale_upper = derivative_scale_bounds(
                word, extension, state['r_bounds'], forbidden_words)
            constant_tag = 0
            if scale_lower == scale_upper:
                constant_tag = constant_scale_ids.setdefault(scale_lower, len(constant_scale_ids) + 1)

            # For tail '31312...', '312' matches through its next-to-last digit.
            # Empty extensions and words beyond the configured depth get flag 0.
            follows_tail = (bool(extension) and len(extension) <= lower_tail_depth
                            and extension[:-1] == minimizing_tail[:len(extension) - 1])

            # Look up the child ends in the parent's exact endpoint dictionary.
            # Extension '1' from default state 0 reuses endpoint IDs (2, 1).
            endpoint0, endpoint1 = (state['endpoints'][value]
                                   for value in tail_endpoints(word, extension, forbidden_words))
            record = (
                child_id, int(follows_tail), constant_tag,
                (DENOMINATOR * scale_lower).floor(),
                (DENOMINATOR * scale_upper).ceil(),
                endpoint0, endpoint1,
            )
            output.write(' '.join(map(str, record)) + '\n')


def write_metadata(output, args, representatives, extension_words, extension_pairs, forbidden_words):
    """Write JSON settings and labels in the same ID order as the V2 numeric input.

    Store words as digit arrays, including [] for the empty extension.
    Store rational values as exact fraction strings. With default settings,
    keys[0] is [0, 0, [1, 2]], prototypes[0] is [1, 2], and the first four
    extensions are [[], [1], [2], [3]]. Pair [0, 1, 0] appends '1' on the
    right. The first two bands are ['0', '1'] and ['0', '1/16'].

    Radicand identifies the quadratic field containing the extremal tails.
    Prehistory interval is the z range used to compute each state's r bounds.
    """
    state_keys = sorted(representatives)
    bands = [(Fraction(0), Fraction(1))]
    bands += [(Fraction(i, args.grid), Fraction(i + 2, args.grid))
              for i in range(args.grid - 1)]
    metadata = {
        # Generation settings. Base is normalized, so '1.02' becomes '51/50'.
        'format': 'FREIMAN_DYADIC_GRAPH_V2',
        'language': args.forbidden,
        'forbidden': [list(map(int, word)) for word in forbidden_words],
        'memory': args.memory,
        'length': args.length,
        'lower_tail_depth': args.lower_tail_depth,
        'macro': args.macro,
        'grid': args.grid,
        'base': str(args.base),
        'low': args.low,
        'high': args.high,
        # Labels indexed by state ID, extension ID, pair ID, and interval type.
        'keys': [[matched, parity, list(map(int, suffix))]
                 for matched, parity, suffix in state_keys],
        'prototypes': [list(map(int, representatives[key])) for key in state_keys],
        'extensions': [list(map(int, word)) for word in extension_words],
        'pairs': extension_pairs,
        'bands': [[str(lower), str(upper)] for lower, upper in bands],
        # Exact-arithmetic conventions used for state geometry.
        'radicand': {'313': 5, '31313': 462, '31313,13131': 41667}[args.forbidden],
        'prehistory_interval': ['1/4', '4/5'],
    }
    json.dump(metadata, output, indent=2)
    output.write('\n')


if __name__ == '__main__':
    # From the repository root, run with a fresh output path.
    #   sage -python -B Markov_interior/prepare.py --output /tmp/demo --grid 4 \
    #       --length 1 --lower-tail-depth 0 --base 3/2 --low -1 --high 0
    args = parse_args()
    forbidden_words = tuple(args.forbidden.split(','))
    representatives = representative_prefixes(args.memory, forbidden_words)
    extension_words, extension_pairs = candidate_extensions(args, representatives, forbidden_words)
    path = args.output.expanduser().with_suffix('.dat')
    meta_path = path.with_suffix('.meta.json')
    path.parent.mkdir(parents=True, exist_ok=True)
    with StringIO() as output, StringIO() as meta_output:
        # One line with the format tag, counts, and ratio-bin limits.
        #   FREIMAN_DYADIC_GRAPH_V2 26 4 -1 0 4 6
        write_header(output, args, state_count=len(representatives),
                     extension_count=len(extension_words), pair_count=len(extension_pairs))

        # Write grid lines of scaled endpoints, starting with [0, 1].
        # The four lines below are the complete output of this step for --grid 4.
        #   0 281474976710656
        #   0 140737488355328
        #   70368744177664 211106232532992
        #   140737488355328 281474976710656
        write_relative_intervals(output, args.grid)

        # Write one left ID, right ID, and flag per line. The example has six pairs.
        #   0 1 0
        #   0 2 0
        #   0 3 0
        #   1 0 0
        #   2 0 0
        #   3 0 0
        write_extension_pairs(output, extension_pairs)

        # Write the two enclosing numerators for each cut. The example has
        # three cuts at 2/3, 1, and 3/2, in that order.
        #   187649984473770 187649984473771
        #   281474976710656 281474976710656
        #   422212465065984 422212465065984
        write_ratio_cuts(output, args.base, args.low, args.high)

        # Write each state's width, information, endpoints, and transitions.
        # With the example's four extension words, state (0, 0, '12') begins with
        #   124905066861958 126493390753360
        #   0 100526777396662 110142382191127 0 6
        # followed by six endpoint rows and four transition rows.
        write_state_data(output, representatives, extension_words, forbidden_words, args.lower_tail_depth)

        # Write matching settings and ID labels to the JSON buffer.
        # In the example, extensions is [[], [1], [2], [3]], and
        # lower_tail_depth is 0. A decimal base such as '1.5' becomes '3/2'.
        write_metadata(meta_output, args, representatives, extension_words, extension_pairs, forbidden_words)

        # Create both files after all calculations. If either save fails,
        # remove files created in this attempt. Exclusive mode protects existing files.
        with ExitStack() as rollback:
            with path.open('x', encoding='ascii') as destination:
                rollback.callback(path.unlink)
                with meta_path.open('x', encoding='ascii') as meta_destination:
                    rollback.callback(meta_path.unlink)
                    destination.write(output.getvalue())
                    meta_destination.write(meta_output.getvalue())
            rollback.pop_all()
