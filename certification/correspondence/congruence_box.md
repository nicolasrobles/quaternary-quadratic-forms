# Source correspondence: Lemma 3.10 and the polynomial-box epsilon consequence

## Scope and frozen source

This review covers both assertions of `lem:box`, Lemma 3.10, and the
separate supplementary obligation `aux:polynomialbox_epsilon`. The
numbered lemma bounds the actual integer points satisfying the dual
quadratic divisibility condition and the exceptional-polynomial
congruences, first without a weight and then with inverse Euclidean norm.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The manuscript and its PDF are unchanged.

| Source location | Reviewed content |
| --- | --- |
| Lines 155–160 and 814–819 | Integral symmetric matrix, determinant, bad-prime modulus, and actual adjugate dual form |
| Lines 562–563 | The unadorned norm is Euclidean; the supremum norm has a separate notation |
| Lines 900–901 | The coefficient-uniform epsilon consequence of Lemma 2.4 |
| Lines 997–1000 | The source modulus, its radical divisibility, and the nonzero bounded-degree polynomials supplied only at primes outside that modulus |
| Lines 1534–1536 | The literal product indicator `Delta_h(u)` and its modulus-one convention |
| `lem:box`, lines 1539–1552 | Positive coprime squarefree moduli, coprimality to the excluded-prime modulus, real radius at least one, and both estimates |
| Lines 1554–1562 | Selection of the prime polynomials, their nonvanishing and degree bounds, and containment in coordinate intervals |
| Lines 1563–1566 | Dyadic summation of the inverse-norm weight |

The final numbered-result endpoint is `source_congruence_box` in
[SourceCongruenceBoxTheorem.lean](../../QuaternaryQuadraticForms/SourceCongruenceBoxTheorem.lean).
The supplementary endpoint is `source_polynomial_box_epsilon` in
[PolynomialBoxEpsilon.lean](../../QuaternaryQuadraticForms/PolynomialBoxEpsilon.lean).
These are distinct certification obligations. Lemma 3.11 and its product
expansion remain separate from this review.

## Source objects and quantifiers

Write `q` for the manuscript's `q_1`, and `m=q*h`.

| Manuscript object | Lean object or exact representation |
| --- | --- |
| Integral symmetric nonsingular matrix `A` | `Matrix (Fin 4) (Fin 4) Int`, with symmetry and nonzero determinant |
| `F*(u)` | `dotProduct u (A.adjugate.mulVec u)` as an actual integer |
| `N_F=2*abs(det A)` | The existing `quadraticBadPrimeModulus A` |
| `rad(N_F)` divides `N` | The existing `primeRadical` divisibility hypothesis |
| Polynomial `D_p` supplied at a prime outside `N` | `D : ∀ p : Nat, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)` |
| Nonzero bounded-degree polynomial | Formal polynomial nonvanishing and a bound on `totalDegree` |
| Euclidean `norm(u)` | `integerEuclideanNorm u`, the standard `EuclideanSpace Real (Fin 4)` norm after coordinatewise integer-to-real casting |
| `Delta_h(u)` | `sourceExceptionalIndicator N D h hhN u`, the actual product of the supplied local zero indicators over the prime divisors of `h` |
| Unweighted source solution set | `sourceCongruenceEuclideanSet A N D q h hhN U`, a literal set of integer tuples |
| Weighted summation range | `divisibleEuclideanBall A q U`, with membership proved equivalent to `0 < norm(u) ≤ U` and `q ∣ F*(u)` |
| Weighted source expression | The sum of `sourceExceptionalIndicator N D h hhN u / integerEuclideanNorm u` over that exact finite range |

The source endpoint allows a real degree bound `E >= 1`. It takes the
natural ceiling of `E` internally and proves that every supplied degree
is at most this ceiling. This accounts for the fact that Section 3 does
not specify that `E` is an integer. The finite-field polynomial-box
theorem is applied with the natural bound `max 2 (Nat.ceil E)`.

For every `E >= 1` and `epsilon > 0`, the endpoint chooses one positive
constant before the matrix, `N`, polynomial family, both moduli, and the
real radius. The same constant bounds both conclusions. Thus the type
encodes exactly the stated dependence on `E,epsilon`, including
independence from every polynomial coefficient. It even permits the
matrix to vary after the constant is chosen.

The source hypotheses `N >= 1`, `q,h >= 1`, squarefreeness, `q.Coprime h`,
and `(q*h).Coprime N` are retained. The proof only needs symmetry and
nonsingularity of `A`; the manuscript's further nonsquare determinant
condition plays no role in this counting lemma. Neither the functions
`xi_p` nor their Fourier estimates enter this result.

## Complete module and interface mapping

All project declarations below are in namespace
`QuaternaryQuadraticForms`. This milestone has 37 public theorem exports
in ten modules. Definitions are kept distinct from theorem exports and
from numbered or supplementary results.

| Module | Exports | Reviewed role and principal interfaces |
| --- | ---: | --- |
| [PrimeFactorEpsilon.lean](../../QuaternaryQuadraticForms/PrimeFactorEpsilon.lean) | 1 | `primeFactor_pow_le_rpow`: uniform small-power bound for a fixed base raised to the number of prime factors |
| [PolynomialBoxEpsilon.lean](../../QuaternaryQuadraticForms/PolynomialBoxEpsilon.lean) | 2 | `polynomialBox_squarefree_card_le_rpow` and `source_polynomial_box_epsilon`: finite integer-box helper and complete arbitrary-interval supplementary endpoint |
| [EuclideanIntegerBox.lean](../../QuaternaryQuadraticForms/EuclideanIntegerBox.lean) | 10 | Literal Euclidean norm, its square-root identity and coordinate bounds, nonzero integer radius at least one, exact finite ball membership, monotonicity, and the coordinate-interval cardinality bound |
| [CongruenceBoxDefinitions.lean](../../QuaternaryQuadraticForms/CongruenceBoxDefinitions.lean) | 7 | Actual product indicator, congruence solution set and weighted sum; exact membership and conversion of the indicator-weighted sum to the reciprocal-norm sum over nonzero solutions |
| [CongruenceBoxPolynomials.lean](../../QuaternaryQuadraticForms/CongruenceBoxPolynomials.lean) | 4 | Actual combined prime polynomials, nonvanishing and degree bounds, squarefree divisibility equivalence, and exact equivalence of all prime equations to the source arithmetic conditions |
| [CongruenceBoxCount.lean](../../QuaternaryQuadraticForms/CongruenceBoxCount.lean) | 2 | Containment of actual Euclidean solutions in the coordinate polynomial box and `congruenceEuclideanBall_card_le_rpow` |
| [InverseNormBoxBound.lean](../../QuaternaryQuadraticForms/InverseNormBoxBound.lean) | 1 | `inverseRadiusSum_le_of_sublevel_card`: finite halving proof of the inverse-radius estimate from actual sublevel counts |
| [CongruenceBoxTheorem.lean](../../QuaternaryQuadraticForms/CongruenceBoxTheorem.lean) | 1 | `congruenceBox_bounds`: both estimates, with one positive constant uniform in all arithmetic data |
| [SourceExceptionalPolynomials.lean](../../QuaternaryQuadraticForms/SourceExceptionalPolynomials.lean) | 5 | Extension of the source-only polynomial family, exact preservation at good primes, original product indicator, and `Delta_1=1` |
| [SourceCongruenceBoxTheorem.lean](../../QuaternaryQuadraticForms/SourceCongruenceBoxTheorem.lean) | 4 | Literal source set and weighted-sum bridges, finiteness, natural-degree endpoint, and real-degree endpoint `source_congruence_box` |

## The polynomial-box epsilon consequence

Let `C >= 1` and `epsilon > 0`. The proof chooses a natural number
`B > C^(1/epsilon)`, before the positive squarefree modulus `m`.
Every prime `p >= B` satisfies `C <= p^epsilon`. For the smaller primes,
`C <= C*p^epsilon`, since `p^epsilon >= 1`.

Multiplying these inequalities over the distinct prime divisors of `m`
gives

\[
C^{\omega(m)}\le C^B m^\varepsilon.
\]

The exponent of the small-prime correction is at most `B`, because those
primes belong to the finite set of natural numbers below `B`.
Squarefreeness supplies the exact product identity `product_(p|m) p=m`.
All products include the empty-prime case `m=1`, and the chosen constant
is positive and independent of `m`.

Applying this to the already proved
`C=C_(n,E)=E+...+E^n` gives

\[
\#\{\text{actual polynomial-box solutions}\}
\le K_{n,E,\varepsilon}m^\varepsilon
 \left(\frac{Y^n}{m}+Y^{n-1}\right).
\]

The supplementary source endpoint retains arbitrary real intervals,
the source-only polynomial domain, and the literal integer solution set
from Lemma 2.4. It returns finiteness together with the bound. The
constant is chosen before the modulus, polynomials, intervals, and `Y`.
The epsilon statement is proved internally and introduces no new
literature input.

## The actual Euclidean lattice and coordinate box

The formal norm is the standard Euclidean norm, with proved identity

\[
\operatorname{integerEuclideanNorm}(u)
=\sqrt{\sum_{i=1}^4 (u_i:\mathbb R)^2}.
\]

Each real-cast coordinate has absolute value at most this norm. Thus a
vector of norm at most `U` belongs to the integer coordinate box

\[
[-\lfloor U\rfloor,\lfloor U\rfloor]^4\cap\mathbb Z^4.
\]

The exact finite interval cardinality and `floor U <= U` show that each
coordinate interval has at most `2U+1 <= 3U` integer points for `U >= 1`.
No integrality of `U` is used. The finite ball is defined by filtering
this box by the Euclidean radius condition, and its membership theorem
is precisely `norm(u) <= U`. Its finiteness is therefore a theorem about
the actual bounded lattice set.

If an integer vector is nonzero, at least one integer coordinate is
nonzero and has absolute value at least one. The Euclidean coordinate
bound then gives `norm(u) >= 1`. This is the discrete fact that closes
the final shell in the weighted argument. Zero norm is proved
equivalent to the zero vector.

## Prime polynomials and the unweighted count

For the positive coprime squarefree integers `q,h`, the product `m=q*h`
is squarefree. At each prime dividing `m`, define the actual polynomial

\[
P_p=\begin{cases}
F^*\bmod p,&p\mid q,\\
D_p,&p\mid h.
\end{cases}
\]

Coprimality of `q,h` makes these cases disjoint. The exact equivalence
between the resulting prime equations and
`q divides F*(u)` together with `Delta_h(u)=1` is proved in
`boxCongruencePolynomial_eval_eq_zero_iff`, using the squarefree prime
product for `q`. Polynomial evaluation is always at the actual
coordinatewise reduction of the integer tuple.

Every prime dividing `m` lies outside `N`. The source radical condition
therefore excludes primes dividing `N_F=2*abs(det A)`. At a prime
dividing `q`, this gives odd characteristic and nonzero reduced
determinant. The adjugate matrix remains symmetric, and its determinant
is the cube of the reduced determinant. The existing matrix-polynomial
theorem then proves that the reduced dual quadratic polynomial is
nonzero. Its degree is at most two. At a prime dividing `h`, the supplied
source nonvanishing and degree hypotheses apply to `D_p`.

The combined degree is at most `max 2 E` for the natural-degree helper,
or `max 2 (Nat.ceil E)` for the real source bound. With `n=4` and `Y=3U`,
the epsilon consequence of Lemma 2.4 yields the bound for the containing
coordinate box. The actual Euclidean solution set is a proved subset
of that polynomial box. Finally,

\[
\frac{(3U)^4}{m}+(3U)^3
\le81\left(\frac{U^4}{m}+U^3\right).
\]

This gives the first source assertion with a constant depending only
on the degree bound and epsilon. No condition on the values `D_p(0)`
is assumed or required.

## The inverse-norm weight

The original product indicator takes only the values zero and one.
The formal proof first establishes the exact equality between the
source sum

\[
\sum_{\substack{0<\lVert u\rVert\le U\\q\mid F^*(u)}}
 \frac{\Delta_h(u)}{\lVert u\rVert}
\]

and the sum of `1/norm(u)` over the nonzero vectors in the unweighted
congruence solution set. This is an equality of actual finite sums;
zero-indicator terms are removed by their proved zero value.

The numerical helper is applied with `B=K*m^epsilon`, where the
unweighted count gives, for every real `T >= 1`,

\[
\#\{u\in s:\lVert u\rVert\le T\}
\le B\left(\frac{T^4}{m}+T^3\right).
\]

Here `s` is the actual finite set of nonzero congruence solutions at the
chosen radius `U`. Its sublevel set is proved to be a subset of the
actual congruence solution set at radius `T`. Every radius in `s` lies
between one and `U`.

The helper proves the dyadic estimate by finite-set induction. For a
nonempty set, let `M` be its largest radius and split at `M/2`. Every
outer point has inverse radius at most `2/M`, so its total contribution
is at most

\[
2B\left(\frac{M^3}{m}+M^2\right).
\]

The inner set is a strict subset because a maximal-radius point is
outside it. When `M/2 >= 1`, induction bounds its contribution by

\[
3B\left(\frac{(M/2)^3}{m}+(M/2)^2\right)
\le\frac34B\left(\frac{M^3}{m}+M^2\right).
\]

When `M/2 < 1`, the inner set is empty. Consequently the full sum is
at most `3B*(M^3/m+M^2)`, and monotonicity permits replacing `M` by `U`.
This is the manuscript's dyadic halving argument expressed by a finite
induction, with every final-shell and real-radius case explicit. It
produces an absolute factor three and no logarithmic loss.

The theorem `congruenceBox_bounds` increases the unweighted constant by
this factor and uses the resulting one positive constant for both
clauses. The source wrapper preserves that common constant.

## Source-family restriction, finiteness, and boundary cases

The final endpoint receives `D_p` only for primes outside `N`. Its
internal total extension is zero elsewhere, and the proof establishes
that every factor of every relevant indicator uses an originally
supplied polynomial. The source indicator is defined as the literal
product of those supplied zero indicators. The helper extension
therefore introduces no additional polynomial-domain hypothesis.

The theorem `sourceCongruenceEuclideanSet_eq` identifies the literal
source set exactly with the finite internal set. The endpoint returns
its finiteness before the numerical `Set.ncard` bound. The weighted
range has exact membership `0 < norm(u) <= U` and `q divides F*(u)`.

The reviewed boundary cases include:

- `q=1`, `h=1`, or both: prime products and congruence conditions have
  their correct empty-product meanings, with `Delta_1(u)=1`.
- `U=1` and nonintegral `U`: exact floor intervals and the final halving
  step preserve every possible integer vector.
- The zero vector: it remains in the unweighted count exactly when
  the source conditions permit it and is excluded from the weighted
  sum by its positive-norm condition.
- Constant nonzero `D_p`: the actual zero indicator vanishes, so the
  source solution set and weighted sum behave correctly.
- Different polynomials at different primes, and degrees at least
  the characteristic: Lemma 2.4 provides the required full uniformity.
- Real degree bound `E=1` or nonintegral `E`: taking the natural ceiling
  preserves degree control and constant dependence.

## Verification and trust boundary

The source proof and both clauses require no manuscript correction.
All polynomial, radical, divisibility, finite-set, norm and summation
bridges are proved internally using the pinned official library and
the previously verified project results. No new literature premise is
introduced. In particular, this proof does not need to reopen the
Section 4 construction of exceptional polynomials: Section 3 supplies
their nonvanishing and degree hypotheses directly.

The strict complete-source target build passed. Actual declaration-kind,
full-type and axiom inspection passed for all 37 new exports. Each has
exactly the standard dependencies `Classical.choice`, `Quot.sound`, and
`propext`; none uses any registered literature premise. The final source
type includes the real degree parameter, the original good-prime
polynomial domain, the common constant chosen before all other data,
finiteness, and both literal source conclusions.

Compilation, actual declaration-type and axiom inspection, source
correspondence, aggregate verification, and independent exact-commit CI
are separate checks. Their observed outcomes, complete export records,
and archived raw evidence are recorded in the live ledger, verification
report, `README.md`, and `CHECKPOINT.md`.
