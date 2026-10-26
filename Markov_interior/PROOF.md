# Proof of the interior intervals

This document supplies the infinite arguments used by `verify.py`. Together
with the exact finite checks in this directory and the fixed files in
`certificates/`, it establishes the stated interval inclusions. No archived
program, archived success flag, search log, or numerical sample is a premise.

The verification is a computer-assisted analytic proof. The separate Lean
project formalizes the original interior-interval result; this document does
not assert a new Lean theorem for the extended language or endpoints.

## Definitions and claims

For a finite word $a$, let $F_a(t)=[0;a_1,\ldots,a_h+t]$, with
$F_\varnothing(t)=t$. For a bi-infinite sequence $z$ of positive integers, put

$$
\lambda_n(z)=[z_n;z_{n+1},\ldots]+[0;z_{n-1},z_{n-2},\ldots],
\qquad m(z)=\sup_n\lambda_n(z).
$$

The Markov spectrum consists of finite values $m(z)$. The usual
continued-fraction characterization of the Lagrange spectrum uses the limsup
of the corresponding local values along a one-sided infinite word. Below we
construct such words explicitly when invoking membership in $L$.

The fixed inputs establish, with the decimal endpoints interpreted as exact
rationals,

$$
[4.52578,4.52754]\subset L\cap M,
\qquad [4.52173315,4.52762938]\subset L\cap M,
\qquad [4.51104888,4.52]\subset L\cap M.
$$

All three intervals are strictly below Freiman's constant. In particular their
open intervals consist of interior points of $M$. No maximality statement or
proof of the whole conjectured $[4.1,4.52]$ region follows.

There are two tail languages, over digits $1,2,3$: one forbids `31313`, and the
other forbids both `31313` and `13131`. Fixed outward prefixes may contain 4;
their infinite appended parts use only $1,2,3$. Each forbidden word is a
palindrome of length five and contains no 2.

## 1. Exact meanings of the finite input

For an outward prefix $a$, let $K(a)$ be its compact set of legal infinite tails.
The state consists of the forbidden-prefix suffix and the parity, together
with a finite suffix controlling the reversed continuant ratio $r$.
The extrema of a legal tail are obtained in alternating lexicographic order.
Every legal finite choice extends by infinitely many 2s, so no selected branch
is a dead end. The finite state/parity process eventually repeats; its periodic
tail is a positive root of the quadratic fixed-point equation for $F_w$.

`prepare.py` computes these extrema exactly in $\mathbb Q(\sqrt{462})$ or
$\mathbb Q(\sqrt{41667})$. `audit.py` recomputes their meanings with a separate
quadratic implementation. It checks endpoint aliases, state transitions,
derivative constants and child shape inclusions. Numeric enclosures are rounded
outward to denominator $2^{48}$; shared endpoint IDs denote exact equalities.

Write $[L(a,b),H(a,b)]$ for the hull of $K(a)+K(b)$ and $W=H-L$.
The interval type $(p,q)$ denotes

$$J_{p,q}(a,b)=[L+pW,L+qW],\qquad 0\le p<q\le1.$$

The continuous variables are the two reversed continuant ratios and the
positive derivative ratio
$S=|F_b'(\xi_b)|/|F_a'(\xi_a)|$, where the tails $\xi_a,\xi_b$ attain the lower
one-sided endpoints. Ratio boxes are closed intervals with endpoints powers
of $51/50$.

For each adopted row, `kernel.cpp` verifies a finite successor cover throughout
the entire parameter box. Each successor appends a nonempty total number of
digits, remains legal, and maps into adopted child rows. When its ratio image
meets several boxes, every box required by the enclosure must be adopted.
Both endpoint inequalities for each overlap are checked using integer interval
arithmetic. A fixed connected component must reach both parent endpoints.
The covers thus hold uniformly over real parameters, not just at sampled points.
Floating-point ordering is only a discovery aid; accepted inequalities are exact.

The checker holds the supplied adoption array fixed and rejects any failed row.
It does not delete a failed row and then call the original certificate valid.
The original 3,464,816 membership bits are retained. Its numeric geometry is
regenerated in the same uniform format used for the 4,260,954-row table; this
does not replace or change the original Freiman/Lean input elsewhere in the repo.

## 2. From a closed cover to actual infinite continued fractions

Fix any point $t$ in an admitted root band. Its successor cover supplies a
child band containing $t$, with an adopted destination row. Repeat indefinitely.
The outward words are nested and remain legal.

At least one digit is appended at each step. In a finite family the derivative
ratio has a strictly positive lower bound and finite upper bound. Since

$$ |F_a'(u)|=1/(q_a+q_{a^-}u)^2 $$

and the allowed $u$ and continuant ratios are bounded, this forces the two
denominators to remain comparable. If only one outward word grew indefinitely,
its denominator would tend to infinity while the other stayed bounded,
contradicting the derivative-ratio bounds. Thus both words grow indefinitely.

Their full continued-fraction cylinders are nested and have widths tending to
zero. At every step $t$ is in the sum of the two full cylinder hulls, even
though a selected auxiliary band need not be contained in its parent band.
The two limiting legal infinite continued fractions therefore sum to $t$.
The conclusion holds for every real point in the root band.

`proof.py:Table.check_row` checks that each concrete root has the stated state,
shape bounds, ratio box and adopted types, and that those types cover its whole
declared band. These are fresh checks of `roots.json`, not inherited claims
from the discovery output.

## 3. Bounds at all noncentral positions

Add the declared central digit $c$. The construction above gives
$\lambda_0=c+t$. To obtain a Markov value, bound every other position uniformly
over the legal tails.

First, enumerate the legal five-letter windows in a completely legal bilateral
tail sequence. The separate exact extrema of the past and future bound every
local value; the window already contains every forbidden word that could
cross the current digit. `proof.py` verifies the exact maxima

$$B_{31313}=4\sqrt{462}/19,\qquad
B_{31313,13131}=4\sqrt{41667}/181.$$

For a root with outward prefixes $a,b$, the backward value at the right core
boundary has the form $F_{b^{rev},c,a}(\alpha)$. Bound its entire range $X$ by
rational outer enclosures of the allowed opposite tails. For every legal first
four digits $v$ of the appended right tail, `compatible_past` checks

$$X\subset\operatorname{conv}\{[0;\eta]:v^{rev}\eta\text{ is a legal past}\}.$$

The comparisons use the safe directions of rational enclosures of the legal
minimum and maximum. At any later appended position, the backward value is a
monotone fractional-linear function of the boundary value. Choose the legal
extremal past that does not decrease it, while retaining the same future.
Four digits capture all boundary restrictions because the forbidden words are
palindromes of length five. The resulting whole comparison sequence is legal,
so its local value is at most $B$. The original appended position is therefore
also at most $B$. The same argument applies to the left tail.

The finitely many noncentral positions in the fixed core are bounded separately
by rational tail enclosures. If the interface condition does not hold, the
alternative `RationalBounds.root` checks every legal near prefix through a fixed
backward depth. Beyond that depth, all retained backward digits are in the legal
tail, and terminal enclosure $[0,1]$ covers every more distant past. Digits 1 and
2 have local value below 4; the digit-3 windows are exhaustively bounded. This
alternative is still a uniform bound at all positions, not a finite sample.

A bound for an ancestor also applies to a root obtained by legally extending
both outward prefixes, since its possible sequences form a subset with the
same central position. This inheritance is checked by actual prefix matching.

Only the part of each root band above its proven noncentral bound is retained.
For every retained target $x$, the constructed sequence satisfies
$\lambda_0=x$ and $\lambda_n\le x$ for all $n\ne0$, hence $m(z)=x$.
This proves membership in $M$.

## 4. Lagrange membership and bulk endpoints

Let $x>B$ be such a realized central maximum. Reproduce longer and longer finite
blocks around its core, separated by 2s. A forbidden word cannot cross these
joins. Within a fixed radius of each copied core, the local values approach
those of the realizing sequence uniformly as the copied blocks grow.
Away from the core, a radius-$R$ window is legal; extending it by 2s gives a
legal bilateral comparison sequence. The continued-fraction error bound gives

$$\lambda_j\le B+2/F_{R+1}^2,$$

where $F_1=F_2=1$. Choose $R$ with $2/F_{R+1}^2<x-B$, then let the copied block
lengths grow. The central values approach $x$, and the limsup at all other
positions is at most $x$. This gives a one-sided infinite continued fraction
with Lagrange value $x$.

For every claimed rational component, `proof.py` checks a positive margin above
$B$ and computes an $R$ making the error smaller than half that margin.
The exact bulk endpoint itself is realized by the periodic word `313121` or
`3131213132`: every periodic position is checked algebraically and its maximum
is exactly $B$. Periodicity makes its supremum and limsup agree.

## 5. The claimed intervals

The verifier recomputes every root band's exact endpoints and its noncentral
bound, unions the retained intervals and rounds displayed endpoints inward by
exact comparisons. Intervals from the two different quadratic fields are
joined only after inward rational rounding.

It separately checks the original paper's 25 root bands and verifies the
original target $[4.52578,4.52754]$. The extension roots establish the other two
claimed rational intervals and their overlap. A rational lower enclosure of
$\sqrt{462}$ proves that all reported components lie strictly below

$$c_F=(2221564096+283748\sqrt{462})/491993569.$$

Changing a root ratio box or supplying an incompatible replacement past is
rejected by controls using the actual verification functions. The optional
second C++ checker repeats every adopted row independently. These checks detect
implementation errors; the proof also relies on the analytic arguments above
and the stated compiler/runtime execution boundary.
