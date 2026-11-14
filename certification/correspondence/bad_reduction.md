# Source correspondence: Lemma 4.1(i)

## Frozen statement and exports

The source is the frozen v35 manuscript
[`quadratic_character_sums_github.tex`](../../manuscript/quadratic_character_sums_github.tex),
SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
This review covers part (i) of Lemma 4.1 (`lem:exceptional`), with the
smoothness condition (1.9) (`eq:smooth`), height `H_G` defined immediately
before it, and modulus (1.10) (`eq:NG`).

For the fixed quadratic form `F` and degree `n ≥ 2`, part (i) asserts that
every admissible integral form `G` has only finitely many bad-reduction
primes outside `N_F` and that `N_G` is bounded by a fixed power of `H_G`,
with constants depending only on `F,n`.

The principal export is
`QuaternaryQuadraticForms.badReductionPrimes_finite_and_height_bound` in
[`BadReductionHeight.lean`](../../QuaternaryQuadraticForms/BadReductionHeight.lean).
Its quantifier order is

```text
∀ A n, 2 ≤ n →
  ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
    ∀ G, G.IsHomogeneous n → SmoothCharacteristicZero A G →
      ∃ hfinite : (badReductionPrimes A G).Finite,
        polynomialBadPrimeModulus A G hfinite
          ≤ K * (polynomialCoefficientHeight G) ^ C.
```

Thus `C,K` are fixed before `G`. The natural number `C` supplies the
source exponent `C_{F,n}`, and `K` supplies its implied constant.
`polynomialBadPrimeModulus_height_bound` proves the same inequality for
every proof of finiteness of the defining bad-prime set.
`badReductionPrimes_finite_of_smooth` separately supplies that finiteness
from the source smoothness hypothesis.

## Literal arithmetic and geometric objects

| Source object or condition | Formal realization |
| --- | --- |
| `F(x) = xᵀ A x` | `matrixQuadraticPolynomial A`, with its proved evaluation identity |
| `n ≥ 2` and an integral form `G` of degree `n` | `2 ≤ n`, `G : MvPolynomial (Fin 4) ℤ`, and `G.IsHomogeneous n` |
| Rank two at every nonzero common zero over `ℚ̄` | `SmoothCharacteristicZero A G`, using the actual formal gradients of the two integral polynomials mapped to `AlgebraicClosure ℚ` |
| Good reduction at a prime | `GoodReductionAt p A G`, with the same rank condition after reduction and extension to `AlgebraicClosure (ZMod p)` |
| `N_F = 2 |det A|` | `quadraticBadPrimeModulus A` |
| Bad primes outside `N_F` | `badReductionPrimes A G`, the set of prime numbers not dividing `N_F` at which the actual rank condition fails |
| `H_G` | `polynomialCoefficientHeight G = max 2 (G.support.sup (fun m => (G.coeff m).natAbs))` |
| `N_G` | `primeRadical N_F` times the product of the distinct primes in `badReductionPrimes A G` |

The height is the manuscript's height, including the lower bound two.
Coefficients outside the finite support are zero, and
`natAbs_coeff_le_polynomialCoefficientHeight` bounds every coefficient.
The modulus uses the intrinsic bad-prime set. Selecting a resultant value
does not enlarge or replace that set.

The manuscript assumes that `A` is symmetric, nonsingular, and has nonsquare
determinant. The elimination and height exports do not need these extra
restrictions: they are valid for the actual matrix polynomial under the
stated characteristic-zero rank condition. Their application to the
manuscript retains its fixed matrix and its nonzero `N_F`. This broader
range does not add any hypothesis to the source theorem.

## The equations and their universal coefficients

The manuscript uses `F`, `G`, and six minors of order two of the two
gradient rows. The implementation uses all ordered pairs of columns:
`BadReductionIndex = Fin 2 ⊕ (Fin 4 × Fin 4)`, of cardinality eighteen.
Its first two entries are `F,G`, and the others are

\[
 M_{ij}=\partial_iF\,\partial_jG-\partial_jF\,\partial_iG.
\]

Four entries are zero because `i=j`; reversing a pair negates its minor.
These additions preserve the eight-equation common zero locus in every
characteristic. `rank_two_ne_iff_minors_zero` proves that the ordered
minors vanish precisely when the two actual rows fail to have rank two.
`badReductionSystem_zero_iff` and
`exists_badReductionSystem_eval₂_zero_iff` establish the corresponding
equivalence for the literal polynomial system and its nonzero zeros.

`badReductionSystem_homogeneous` proves that `F` has assigned degree two
and all other seventeen equations have assigned degree `n`.
The derivative products have degree `1+(n-1)=n`; a zero minor retains
that degree of homogeneity. No division by the degree or exclusion of
primes dividing `n` enters this calculation.

[`GenericQuadricFamily.lean`](../../QuaternaryQuadraticForms/GenericQuadricFamily.lean)
fixes `A` and replaces each degree-`n` coefficient of `G` by its own
indeterminate. The generic form is a literal finite sum over all
degree-`n` monomials. The specialization theorems reconstruct the original
polynomial from its coefficients and commute with arbitrary coefficient
maps, including reduction from the integers. The gradient minors commute
with those maps as proved in
[`BadReductionSystem.lean`](../../QuaternaryQuadraticForms/BadReductionSystem.lean).

## Elimination and the same integer at every bad prime

The single literature premise used here is
`Trusted.lang_homogeneous_resultants`, registered as
`EXT.LANG_ELIMINATION`. Its exact source and generic-coefficient interface
are documented in [elimination_input.md](elimination_input.md): Lang,
*Algebra*, revised third edition, IX.4.1, p. 402, with the geometric-zero
convention following IX.3.1, p. 389.

That premise supplies integer polynomials in independent generic
coefficients, chosen before the field or specialization.
[`EliminationFamily.lean`](../../QuaternaryQuadraticForms/EliminationFamily.lean)
proves the substitution of the actual coefficient polynomials into that
family. It uses reconstruction of homogeneous forms and composition of
polynomial evaluation. The resulting parameter family remains fixed
before all fields and parameter values.

`badReduction_resultant_family` in
[`BadReductionResultants.lean`](../../QuaternaryQuadraticForms/BadReductionResultants.lean)
specializes this proved construction to the eighteen equations. For fixed
`A,n`, it produces one finite integer family `R_j` such that

\[
 \operatorname{SmoothCharacteristicZero}(A,G)
 \iff \exists j,\ R_j(\operatorname{coeff}G)\ne0,
\]

and for every prime `p`,

\[
 \neg\operatorname{GoodReductionAt}(p,A,G)
 \iff \forall j,\ p\mid R_j(\operatorname{coeff}G).
\]

[`GeometricReduction.lean`](../../QuaternaryQuadraticForms/GeometricReduction.lean)
identifies specialization to `ℚ` or `ZMod p`, followed by algebraic closure,
with direct evaluation of the original integral equations in the same
closure. The characteristic-zero direction uses injectivity of the
integer cast into `ℚ`. The prime-field direction uses the equivalence
between zero reduction and integer divisibility.

Smoothness therefore selects an index `j` with nonzero integer value
`z = R_j(coeff G)`. Every bad-reduction prime divides this same integer.
The index and value can depend on `G`; the family was fixed first.
`exists_nonzero_badReduction_divisor` proves this statement internally.
The bad primes lie among the prime divisors of `|z|`, so their actual set
is finite. No finiteness or common-divisor assertion is added as an axiom.

## Uniform height bound and the actual product

[`PolynomialHeight.lean`](../../QuaternaryQuadraticForms/PolynomialHeight.lean)
proves the elementary bound for each fixed integer polynomial `P`:

\[
 |P(x)|\le
 \left(\sum_m |\operatorname{coeff}_m P|\right)H^{\deg P}
 \qquad\text{when }H\ge1\text{ and }|x_i|\le H.
\]

It bounds the actual monomial expansion and takes maxima over the finite
resultant family, with an additional maximum with one. This supplies
positive integers `C,K`, independent of the evaluation tuple and of `G`.
Applied to the coefficients of `G`, it gives

\[
 |R_j(\operatorname{coeff}G)|\le K H_G^C
\]

for every index. Only afterwards does smoothness select a nonzero value.
`exists_nonzero_badReduction_divisor_height_bound` combines this uniform
estimate with its divisibility by every actual bad prime.

The existing arithmetic lemmas in
[`GoodReduction.lean`](../../QuaternaryQuadraticForms/GoodReduction.lean)
prove that the product of those distinct primes divides `|z|`. Since
`z ≠ 0`, their product is at most `|z|`. Multiplying by the fixed factor
`rad(N_F)` gives

\[
 N_G\le\operatorname{rad}(N_F)|z|
 \le\operatorname{rad}(N_F)K H_G^C.
\]

`polynomialBadPrimeModulus_height_bound` absorbs that fixed factor into
the final positive `K`. The principal export returns both the proved
finiteness and the bound. The quantifiers in the final theorem preserve
the source's uniform dependence on the fixed form and degree.

## Scope and remaining part

This establishes the full content of **Lemma 4.1(i)** relative to the
registered general Lang input. The only additional axiom in its dependency
set is that literature premise; the source-specific equations,
substitution, rank interpretation, common integer, finiteness, and height
bound are proved internally.

**Lemma 4.1(ii) remains Pending.** This record does not assert the
construction of the exceptional plane polynomial `D_p`, its uniform
degree bound, or its transversality consequence. Consequently this review
does not certify the whole two-part Lemma 4.1.

Compilation results, axiom reports, checked hashes, and execution status
are recorded separately from this mathematical correspondence review.
