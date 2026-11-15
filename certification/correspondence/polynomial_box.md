# Source correspondence: Lemma 2.4

## Scope and frozen source

This review covers the complete assertion of `lem:polynomialbox`, Lemma
2.4: the number of actual integer tuples satisfying possibly different
polynomial congruences at every prime divisor of a positive squarefree
modulus, in arbitrary intervals containing at most `Y` integers. The
coefficient-independent constant is exactly

\[
C_{n,E}=E+E^2+\cdots+E^n.
\]

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The manuscript and its PDF are unchanged.

| Source location | Reviewed content |
| --- | --- |
| Lines 827–830 | Uniformity in polynomial coefficients and permission for unrelated polynomials at different primes |
| `lem:polynomialbox`, lines 832–843 | All parameter hypotheses, literal solution count, and exact constant |
| Lines 845–854 | The modulus-one case and the one-variable root/CRT interval estimate |
| Lines 855–867 | Slicing in the first variable, identically zero fibres, and the uniform fibre count |
| Lines 868–873 | The weighted expansion of the degenerate-prime product |
| Lines 874–887 | A nonzero coefficient polynomial at each prime and induction in one fewer variable |
| Lines 889–898 | The two divisor-product estimates, boundary contribution, and exact constant recurrence |

The complete source endpoint is `source_polynomial_box` in
[PolynomialBoxTheorem.lean](../../QuaternaryQuadraticForms/PolynomialBoxTheorem.lean).
The endpoint accepts the source polynomial family only at prime divisors
of `m`, rather than requiring unrelated data at all natural numbers. It
also retains arbitrary real intervals through their order-connected sets
of integer points. The endpoint proves finiteness of the actual solution
set as well as its numerical bound.

The immediately following epsilon-loss consequence at lines 900–901 is
the separate supplementary obligation `aux:polynomialbox_epsilon`. It is
not part of this review's certified scope. Lemmas 3.10 and 3.11 are also
separate obligations.

## Objects, hypotheses, and quantifiers

| Manuscript object | Lean object or exact representation |
| --- | --- |
| `n,E >= 1` | Natural numbers `n,E` with explicit lower bounds |
| Positive squarefree modulus `m` | Natural number `m` with positivity and `Squarefree m` |
| The primes dividing `m` | `m.primeFactors`, with membership proved equivalent to primality and divisibility under the source modulus hypothesis |
| Polynomial supplied at `p` | An actual `MvPolynomial (Fin n) (ZMod p)`; the final source family is indexed only by `{p : Nat // Nat.Prime p ∧ p ∣ m}` |
| Nonzero polynomial | Formal polynomial inequality `P p ≠ 0` |
| Degree at most `E` | `MvPolynomial.totalDegree (P p) ≤ E` |
| Integer box with endpoints | `integerPolynomialBox a b = Fintype.piFinset (fun i => Finset.Icc (a i) (b i))` |
| Simultaneous congruence solutions in integer endpoints | `polynomialBoxSolutions S P a b`, filtering the actual integer box by all actual evaluations in `ZMod p` |
| Literal source solution set | `sourcePolynomialBoxSet m P I`, containing integer tuples whose real coordinate casts lie in the supplied intervals and whose supplied prime polynomials evaluate to zero |
| Arbitrary interval `I_i` | An order-connected subset of `Real`, with explicitly finite integer preimage and its cardinality at most `Y` |
| `C_(n,E)` | `polynomialBoxConstant n E`, proved equal to the literal sum over `Finset.Icc 1 n` |
| `omega(m)` | `ArithmeticFunction.cardDistinctFactors m`, identified with the cardinality of the prime-factor set |

Every polynomial evaluation uses the coordinatewise integer cast into
`ZMod p`. No polynomial is replaced by a numerical majorant before its
literal solution set has been connected to that majorant.

The constant is a specified function of `n` and `E`. Thus the theorem's
quantifiers encode uniformity in the coefficients, the separate choices
of polynomials at different primes, `m`, the intervals and their positions,
and `Y`. There is no hidden choice of a coefficient-dependent constant.

The stronger intermediate theorem `polynomialBox_primeSet_card_le` uses
an arbitrary finite set `S` of distinct primes and its product. The
squarefree-modulus wrapper `polynomialBox_squarefree_card_le` rewrites
that product as `m` and its cardinality as `omega(m)`. Squarefreeness is
used at this source-wrapper step; it is not an assumption that every
integer congruence modulo an arbitrary modulus is already represented by
distinct prime conditions.

## Modules and public proof interfaces

All project theorem names below are in the `QuaternaryQuadraticForms`
namespace. This milestone has 49 public theorem exports in nine modules.
See the live ledger and verification report for complete declaration
records. Definitions are not counted as supporting theorem exports or
numbered results.

| Module | Theorem exports | Reviewed role and principal interfaces |
| --- | ---: | --- |
| [PolynomialBoxSlices.lean](../../QuaternaryQuadraticForms/PolynomialBoxSlices.lean) | 8 | Actual first-variable slicing, evaluation identity, formal zero-fibre criterion, degree bounds, selection of a nonzero coefficient polynomial, and the one-variable base case |
| [PolynomialBoxDefinitions.lean](../../QuaternaryQuadraticForms/PolynomialBoxDefinitions.lean) | 10 | Actual integer boxes and congruence sets, exact membership, product cardinality, empty-prime-set identity, and exact decomposition into first-coordinate fibres |
| [PolynomialBoxIntervals.lean](../../QuaternaryQuadraticForms/PolynomialBoxIntervals.lean) | 4 | Finite integer intervals as integer-endpoint intervals, and exact passage from arbitrary real intervals to their integer points |
| [PolynomialBoxResidues.lean](../../QuaternaryQuadraticForms/PolynomialBoxResidues.lean) | 4 | Distinct-prime CRT uniqueness, injective encoding by prime residues and quotient blocks, and the uniform integer-interval count |
| [PolynomialBoxOneVariable.lean](../../QuaternaryQuadraticForms/PolynomialBoxOneVariable.lean) | 2 | Actual polynomial root sets over each prime field and `polynomialIntervalZeros_card_le` |
| [PolynomialBoxCombinatorics.lean](../../QuaternaryQuadraticForms/PolynomialBoxCombinatorics.lean) | 12 | Exact constant recurrence and its power-sum identities, weighted subset expansion, both product bounds, and `polynomialBox_count_step` |
| [PolynomialBoxFiber.lean](../../QuaternaryQuadraticForms/PolynomialBoxFiber.lean) | 3 | Actual degenerate-prime set, removal of identically zero congruences, and the uniform fibre bound |
| [PolynomialBoxInduction.lean](../../QuaternaryQuadraticForms/PolynomialBoxInduction.lean) | 1 | Induction on the actual dimension and `polynomialBox_primeSet_card_le` |
| [PolynomialBoxTheorem.lean](../../QuaternaryQuadraticForms/PolynomialBoxTheorem.lean) | 5 | Squarefree-modulus, source polynomial-domain and arbitrary-interval bridges; complete source theorem |

## One variable: roots, CRT, and interval cardinality

For a finite set `S` of primes, the one-variable theorem counts exactly

\[
\{t\in[a,b]\cap\mathbb Z:
 P_p(t)=0\text{ in }\mathbb F_p\quad(p\in S)\}.
\]

For each `p`, the finite set of allowed residues is the root set of the
actual polynomial `P_p`. The nonzero-polynomial hypothesis justifies
identifying root membership with evaluation equal to zero. The official
library root bound gives at most the polynomial's degree, and hence at
most `E`, distinct roots. Multiplicities cannot increase the number of
distinct roots.

The residue-count proof uses an injective encoding of an allowed integer
`t` by its tuple of prime residues together with

\[
\left\lfloor\frac{t-a}{\prod_{p\in S}p}\right\rfloor.
\]

Equality of the residue tuples implies congruence modulo the product of
the distinct primes, by the uniqueness part of CRT. Equality of the
quotient blocks then forces equality of the integers. CRT surjectivity
is unnecessary for this upper bound.

There are at most `E^|S|` residue tuples. The block index is bounded by
`(b-a).toNat / product(S)`, and the proof explicitly relates
`(b-a).toNat` to the number of integers in `Finset.Icc a b`. Therefore,
if that cardinality is at most the real number `Y`, the count is at most

\[
E^{|S|}\left(\frac{Y}{\prod_{p\in S}p}+1\right).
\]

No assumption that endpoints are nonnegative or that `Y` is integral is
introduced. The same estimate permits `S` to be empty; this is needed
when a higher-dimensional fibre is identically zero at every imposed
prime.

## Slicing and degenerate fibres

The library equivalence `MvPolynomial.finSuccEquiv` identifies an actual
polynomial in `n+1` variables with a polynomial in its first variable
whose coefficients are actual polynomials in the remaining `n`
variables. The project defines

\[
Q_{p,y}(t)=P_p(t,y)
\]

as `polynomialBoxSlice (P p) y`. Its evaluation is proved equal to the
evaluation of `P_p` at `Fin.cons t y`, and its degree is at most the
total degree of `P_p`.

The set `polynomialBoxBadPrimes S P y` consists exactly of those primes
at which `Q_(p,y)` is the zero formal polynomial. The theorem
`polynomialBoxSlice_eq_zero_iff` proves that this occurs exactly when
every coefficient polynomial vanishes at `y`.

This formal-polynomial distinction matters over finite fields: a
nonzero polynomial can vanish at every element of the field. Such a
polynomial remains in the nondegenerate set, and the ordinary root
bound still applies because its degree is then large enough. The proof
does not confuse these two notions of zero.

For each prime, a nonzero coefficient polynomial is selected from the
nonzero original polynomial. Its total degree is at most `E`. The choice
is fixed for that prime before the base point `y` and the subset of
degenerate primes are varied. Every identically zero fibre forces this
selected coefficient polynomial to vanish at `y`.

Writing

\[
D(y)=\{p\in S:Q_{p,y}=0\},\qquad
g(y)=\prod_{p\in D(y)}p,\qquad
m=\prod_{p\in S}p,
\]

the nondegenerate one-variable theorem applies to `S \ D(y)`. Removal
of the identically zero congruences is proved to preserve the exact
fibre solution set. The product identity for the complementary prime
sets and `E >= 1` then give the manuscript's uniform fibre bound

\[
\#\{t:(t,y)\text{ is a solution}\}
\le E^{|S|}\left(\frac{Yg(y)}m+1\right).
\]

No common nonvanishing direction for the different prime polynomials is
assumed. The first coordinate is fixed throughout, and every degenerate
fibre is accounted for explicitly.

## Weighted subset expansion and exact constant

The formal proof indexes the squarefree divisor calculation by subsets
of the prime set. If `T` corresponds to the divisor
`h = product(T)`, its weight is `product(p-1)` over `T`. This is precisely
the source weight `phi(h)` for squarefree `h`. The Lean calculation
proves the following expansion directly by finite product expansion;
it does not take the source's divisor identity as a premise:

\[
\sum_y\prod_{p\in D(y)}p
=\sum_{T\subseteq S}
  \left(\prod_{p\in T}(p-1)\right)
  \#\{y:T\subseteq D(y)\}.
\]

Indeed, for every fixed `y`, expanding
`product_(p in D(y)) (1+(p-1))` gives the subset sum. The proof then
interchanges two finite sums and identifies the inner sum with the
cardinality of the actual filtered base box.

Let `d >= 1` be the base dimension and `C=C_(d,E)`. The selected
nonzero coefficient polynomials and the induction hypothesis give,
for every subset `T` including the empty subset,

\[
\#\{y:T\subseteq D(y)\}
\le C^{|T|}\left(
 \frac{Y^d}{\prod_{p\in T}p}+Y^{d-1}\right).
\]

The two resulting weighted sums are bounded by the exact product
calculations

\[
\begin{aligned}
\sum_{T\subseteq S}
 \frac{C^{|T|}\prod_{p\in T}(p-1)}{\prod_{p\in T}p}
 &=\prod_{p\in S}\left(1+C\frac{p-1}{p}\right)
 \le(1+C)^{|S|},\\
\sum_{T\subseteq S}C^{|T|}\prod_{p\in T}(p-1)
 &=\prod_{p\in S}(1+C(p-1))
 \le C^{|S|}\prod_{p\in S}p.
\end{aligned}
\]

The first bound uses `C >= 0` and positivity of the primes. The second
uses `C >= 1`. All denominators are products of positive primes, with
the empty product equal to one.

For a nonempty prime set, `k=|S| >= 1` and

\[
C^k+1\le(1+C)^k.
\]

Together with the actual base-box cardinality at most `Y^d`, the fibre
sum is at most

\[
\bigl(E(1+C)\bigr)^k
\left(\frac{Y^{d+1}}m+Y^d\right).
\]

The project constant is defined recursively by
`C_(0,E)=0` and `C_(d+1,E)=E(1+C_(d,E))`, and both range-indexed and
`Icc 1 n` power-sum identities are proved. Thus the recurrence yields
the exact stated constant, without an extra numerical factor or an
unspecified implied constant.

## Source intervals, prime-domain restriction, and boundary cases

The source endpoint uses the literal set of integer tuples whose real
coordinate casts lie in the supplied intervals. For each interval,
order-connectedness passes to its integer preimage under the monotone
integer-to-real cast. A finite nonempty integer interval is exactly
the integer `Icc` between its minimum and maximum. An empty interval
is represented by `Icc 1 0`. The correspondence is proved, so endpoint
openness and nonintegral endpoints do not alter the counted set.

Finiteness of each interval's integer preimage is an explicit formal
version of the source phrase "containing at most `Y` integers." The
proof does not use a totalized cardinality bound to infer finiteness.
The actual solution set is a subset of the finite product of those
integer-point sets, and its finiteness is part of the source endpoint.

The endpoint accepts polynomial data only for prime divisors of `m`.
The internal extension to natural-number indices is used solely to
apply the prime-set theorem. Every evaluation or hypothesis in that
application is restricted back to the actual prime-factor set; values
outside it impose no condition on the source family.

The following cases remain present in the theorem and proof:

- `m=1`: the prime set is empty, no polynomial is required, and the
  actual count is at most `Y^n`, which implies the stated bound with
  `omega(1)=0`.
- `n=1`: the remaining-variable type is `Fin 0`, with its unique empty
  tuple. Specializing the empty tail is injective, so a nonzero input
  remains a nonzero univariate polynomial.
- `E=1` and `Y=1`: every constant and boundary estimate uses weak
  inequalities and remains valid at these endpoints.
- Empty intervals: the actual box or solution set may be empty, and
  the same cardinality and fibre identities apply.
- Nonzero constant polynomials: they have no roots and are included
  without a positive-degree hypothesis at each prime.
- Fibres identically zero at some or all primes: the degenerate-prime
  product and the empty-prime-set one-variable estimate account for
  them explicitly.
- Degrees at least the characteristic: no restriction `E < p` is
  present, and formal nonzero polynomials that induce the zero
  function are permitted.

## Trust boundary and verification scope

This proof introduces no literature premise. Lemma 2.4's manuscript
deductions, including the root-count application, CRT specialization,
interval count, coefficient selection, degeneracy expansion, induction,
and exact constant, are proved using the pinned official mathlib and
the project modules described above.

No previously certified manuscript lemma is required by the new
polynomial-box proof. The four existing registered external premises
remain separate from this result. Proof compilation, declaration-type
inspection, dependency/axiom inspection, and independent exact-commit
verification are distinct checks; their observed results and final
counts belong in the live ledger and execution checkpoint.

The strict complete-source target build passed. A separate inspection
of all 49 actual exported theorem types and their axiom dependencies
also passed. Forty-six exports use only `propext`, `Classical.choice`,
and `Quot.sound`; one uses only `propext`; the two recurrence definition
identities use no axioms. No literature premise enters any new export.
The final source type was independently compared with every clause of
the frozen statement, including the literal power sum, the usual omega
function, the source-only polynomial domain, and the finite actual
solution set.

Aggregate verification and independent exact-commit CI are separate
execution checks. Their successful runs, when observed, and their
archived raw evidence are recorded in `README.md` and `CHECKPOINT.md`.
