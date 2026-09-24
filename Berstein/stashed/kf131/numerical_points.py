#!/usr/bin/env python3
"""Find periodic-tail approximants in K_F(112)+K_F(122), then certify errors.

Decimal arithmetic is only used for discovery. Every reported success is
independently checked with rational continued-fraction bounds. Failed searches
are unresolved; a precision/budget failure is never called a gap.
"""
import argparse
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path
import random
import time


@dataclass(frozen=True)
class Cylinder:
    word: str
    a: int
    b: int
    c: int
    d: int
    lo: Decimal
    hi: Decimal


def make_cylinder(word, matrix, radical):
    a, b, c, d = matrix
    low = (radical-2)/4 if word.endswith('1') else (2*radical-5)/5
    high = (2*radical-5)/3 if word.endswith('13') else (2*radical-4)/3
    ends = [(a*x+b)/(c*x+d) for x in (low, high)]
    return Cylinder(word, a, b, c, d, min(ends), max(ends))


def children(z, radical):
    for k in (1, 2, 3):
        if k == 1 and z.word.endswith('13'):
            continue
        yield make_cylinder(z.word+str(k),
                            (z.b, z.a+k*z.b, z.d, z.c+k*z.d), radical)


def prefix(word, radical):
    z = make_cylinder('', (1, 0, 0, 1), radical)
    for digit in word:
        z = next(c for c in children(z, radical) if c.word[-1] == digit)
    return z


def rational_periodic_bracket(word, repeat=100):
    """Bound [0; word, overline(2)] with two rational continued fractions.

    Extending by 100 twos still leaves a tail in [1/4,4/5]. Computing backwards
    is independent of the discovery code's matrix and radical formulas.
    """
    if any(c not in '123' for c in word) or '131' in word:
        raise ValueError('Illegal witness')
    values = []
    for z in (Fraction(1, 4), Fraction(4, 5)):
        for k in reversed(word+'2'*repeat):
            z = 1/(int(k)+z)
        values.append(z)
    return min(values), max(values)


def certify(target, u, v, epsilon):
    assert u.startswith('112') and v.startswith('122')
    a, b = rational_periodic_bracket(u)
    c, d = rational_periodic_bracket(v)
    error = max(abs(a+c-target), abs(b+d-target))
    assert error < epsilon
    return error


def search(target, epsilon, radical, budget):
    stack = [(prefix('112', radical), prefix('122', radical))]
    visited = 0
    # Discovery has 90+ digits; decisions are deliberately far above roundoff.
    while stack and visited < budget:
        u, v = stack.pop()
        visited += 1
        lo, hi = u.lo+v.lo, u.hi+v.hi
        if not lo <= target <= hi:
            continue
        if hi-lo < epsilon/2:
            return u.word, v.word, visited
        if u.hi-u.lo >= v.hi-v.lo:
            candidates = [(c, v) for c in children(u, radical)]
        else:
            candidates = [(u, c) for c in children(v, radical)]
        scored = []
        for x, y in candidates:
            a, b = x.lo+y.lo, x.hi+y.hi
            if a <= target <= b:
                # Try centrally located targets first, retaining all alternatives.
                score = min(target-a, b-target)/(b-a)
                scored.append((score, x, y))
        scored.sort(key=lambda z: z[0])
        stack.extend((x, y) for _, x, y in scored)
    return None, None, visited


def as_decimal(value, digits=16):
    with localcontext() as context:
        context.prec = digits
        return str(Decimal(value.numerator)/Decimal(value.denominator))


def sample_targets(grid_count, random_count, seed):
    from six_offer_obstruction import GAP_LABELS
    from type_certificates import endpoint
    left, right = Fraction('1.29288'), Fraction('1.292906')
    targets = [('grid', left+(right-left)*k/(grid_count-1)) for k in range(grid_count)]
    rng = random.Random(seed)
    targets += [('random', left+(right-left)*Fraction(rng.randrange(10**30), 10**30))
                for _ in range(random_count)]
    # Probe holes of the previously restricted six-offer construction at every
    # return n=4..40. Search the full original pair, without that restriction.
    for n in range(4, 41):
        u, v = '112'+'2'*n, '122'+'2'*n
        a, b = sorted(endpoint(u, v, label) for label in GAP_LABELS)
        target = Fraction(((a+b)/2).decimal(80))
        assert a < target < b and left < target < right
        targets.append((f'six_offer_hole_n{n}', target))
    with localcontext() as context:
        context.prec = 90
        targets.append(('periodic_limit_nearby', Fraction(2-Decimal(2).sqrt()/2)))
    return targets


def run(grid_count, random_count, exponent, budget, seed):
    start = time.monotonic()
    left, right = Fraction('1.29288'), Fraction('1.292906')
    epsilon = Fraction(1, 10**exponent)
    targets = sample_targets(grid_count, random_count, seed)
    witnesses, failures = [], []
    maximum_error = Fraction(0)
    with localcontext() as context:
        context.prec = max(90, exponent+50)
        radical = Decimal(10).sqrt()
        dec_epsilon = Decimal(1).scaleb(-exponent)
        for index, (kind, target) in enumerate(targets):
            decimal_target = Decimal(target.numerator)/Decimal(target.denominator)
            u, v, visited = search(decimal_target, dec_epsilon, radical, budget)
            if u is None:
                failures.append({'kind': kind, 'target': str(target), 'visited': visited})
            else:
                error = certify(target, u, v, epsilon)
                maximum_error = max(maximum_error, error)
                witnesses.append({'kind': kind, 'target': str(target), 'u': u, 'v': v,
                                  'visited': visited, 'certified_error_upper_decimal': as_decimal(error)})
            if (index+1)%100 == 0:
                print(f'{index+1}/{len(targets)} points: {len(failures)} unresolved', flush=True)
    return {
        'status': 'Finite approximations, not exact target membership or an interior proof',
        'target_interval': [str(left), str(right)],
        'epsilon': str(epsilon), 'exponent': exponent,
        'grid_count': grid_count, 'random_count': random_count, 'seed': seed,
        'stress_count': len(targets)-grid_count-random_count,
        'grid_spacing': str((right-left)/(grid_count-1)),
        'point_count': len(targets), 'success_count': len(witnesses),
        'unresolved_count': len(failures), 'unresolved': failures,
        'max_certified_error_decimal': as_decimal(maximum_error),
        'max_visited': max((w['visited'] for w in witnesses), default=0),
        'total_visited': sum(w['visited'] for w in witnesses)+sum(w['visited'] for w in failures),
        'max_prefix_length': max((max(len(w['u']),len(w['v'])) for w in witnesses), default=0),
        'periodic_tail': '2', 'witnesses': witnesses,
        'elapsed_seconds': round(time.monotonic()-start, 3),
    }


def replay(path):
    data = json.loads(path.read_text())
    expected = sample_targets(data['grid_count'], data['random_count'], data['seed'])
    actual = [(w['kind'], Fraction(w['target'])) for w in data['witnesses']+data['unresolved']]
    assert sorted(actual) == sorted(expected)
    assert data['point_count'] == len(expected)
    assert data['success_count'] == len(data['witnesses'])
    assert data['unresolved_count'] == len(data['unresolved'])
    maximum = Fraction(0)
    for witness in data['witnesses']:
        error = certify(Fraction(witness['target']), witness['u'], witness['v'], Fraction(data['epsilon']))
        maximum = max(maximum, error)
    print(f"Independently replayed {len(data['witnesses'])} rational witness checks; "
          f"maximum error bound {as_decimal(maximum)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--grid-count', type=int, default=1001)
    parser.add_argument('--random-count', type=int, default=500)
    parser.add_argument('--exponent', type=int, default=40)
    parser.add_argument('--budget', type=int, default=100000)
    parser.add_argument('--seed', type=int, default=20260922)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('numerical_points.json'))
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        replay(args.verify)
        return
    if args.grid_count < 2 or args.random_count < 0 or args.exponent < 1:
        parser.error('Require grid-count >= 2, random-count >= 0, exponent >= 1')
    data = run(args.grid_count,args.random_count,args.exponent,args.budget,args.seed)
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k != 'witnesses'}, indent=2))


if __name__ == '__main__':
    main()
