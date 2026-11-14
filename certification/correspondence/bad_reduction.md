# Source correspondence: Lemma 4.1

## Frozen statement and exports

The source is the frozen manuscript
[`quadratic_character_sums_github.tex`](../../manuscript/quadratic_character_sums_github.tex),
SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The first part of this review covers part (i) of Lemma 4.1 (`lem:exceptional`), with the
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

## Scope of the part (i) review

This establishes the full content of **Lemma 4.1(i)** relative to the
registered general Lang input. The only additional axiom in its dependency
set is that literature premise; the source-specific equations,
substitution, rank interpretation, common integer, finiteness, and height
bound are proved internally.

The review of part (ii) follows below. The part (i) argument and its
literature boundary are unchanged.

Compilation results, axiom reports, checked hashes, and execution status
are recorded separately from this mathematical correspondence review.

## Part (ii): frozen statement and final exports

Part (ii) of `lem:exceptional`, source lines 1623-1633, asks for one
positive degree bound depending only on the fixed quadratic form and `n`.
For every admissible `G` and every prime `p ∤ N_G`, there must be a nonzero
polynomial `D_p` over the prime field, of degree at most that bound and
vanishing at the origin. Every normal `u` outside its zero set must satisfy
both `F*(u) ≠ 0` and rank three of the actual rows `∇F(x), ∇G(x), u` at
each nonzero common zero over the algebraic closure satisfying the plane
equation.

The principal export is
`QuaternaryQuadraticForms.exceptional_plane_polynomial` in
[`ExceptionalPlanePolynomial.lean`](../../QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean).
The intermediate export `exceptional_plane_polynomial_over_fields` proves
the construction over any coefficient field where two is nonzero and the
fixed matrix remains nonsingular. Its degree bound is chosen before that
field and before the form.

| Source clause | Content of the final export |
|---|---|
| Fixed `F,n`, with `n ≥ 2` | Integral symmetric nonsingular matrix `A`; `2 ≤ n` |
| One `E_{F,n} ≥ 1` before the varying data | `∃ E : ℕ, 1 ≤ E ∧ ∀ G ... p ...` |
| Source characteristic-zero smoothness | The literal `SmoothCharacteristicZero A G` hypothesis |
| Prime `p ∤ N_G` | `Fact p.Prime` and nondivisibility of the literal `polynomialBadPrimeModulus`; its finiteness proof is supplied by part (i) |
| `D_p ∈ F_p[u_1,...,u_4]` and `D_p ≠ 0` | `D : MvPolynomial (Fin 4) (ZMod p)` and `D ≠ 0` |
| Degree at most `E_{F,n}` | `D.totalDegree ≤ E` |
| Vanishing at the origin | `MvPolynomial.eval 0 D = 0` |
| `F*(u) ≠ 0` outside the exceptional set | Nonvanishing of `dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u)` |
| Full geometric transversality | `PlaneTransverseRank` for the actual reduced polynomials over `AlgebraicClosure (ZMod p)` and the coefficient extension of `u` |

The final theorem uses the source's characteristic-zero smoothness and
the literal good-modulus condition. It does not ask the caller to supply a
finite bad-prime set, a separate good-reduction hypothesis, a transverse
plane, or a nonzero resultant polynomial. Symmetry and nonsingularity of
`A` are the standing source hypotheses. Nonsquareness of its determinant
is not needed for this geometric lemma; omitting it gives a broader
statement without strengthening any source assumption.

## Part (ii): the actual second elimination system

[`RankThreeMinors.lean`](../../QuaternaryQuadraticForms/RankThreeMinors.lean)
defines the literal three-row determinant and proves that all ordered
three-column minors vanish exactly when the three rows fail to have rank
three. The equivalence uses actual matrix rank and linear independence.

[`PlaneReductionSystem.lean`](../../QuaternaryQuadraticForms/PlaneReductionSystem.lean)
forms `F`, `G`, the plane equation, and all 64 ordered three-column minors.
The source instead lists four minors, one for each three-element set of
columns. The extra ordered minors either vanish because a column repeats
or differ from one of those four by sign. More directly, the proved rank
equivalence shows that the resulting 67-equation system has exactly the
required common zero set, in every characteristic.

The assigned homogeneous degrees in the geometric variables are `2,n,1`
for the first three equations, and `n` for every minor. The plane normal
is a coefficient, so a minor has degree `1+(n-1)=n` in those variables.
All assigned degrees are positive. The construction allows zero normal
coordinates and zero specialized equations, as does the registered Lang
interface. Every equation, including the formal gradients, commutes with
coefficient maps.

The theorems `planeReductionSystem_zero_iff`,
`exists_planeReductionSystem_zero_iff`, and
`hasNonzeroGeometricZero_planeReductionSystem_iff` identify the system
with failure of `PlaneTransverseRank`, respectively at a point, over the
coefficient field, and over its algebraic closure. Consequently no
set-theoretic replacement of the manuscript's geometric rank condition
is used.

## Part (ii): one resultant family before all fields and forms

[`ExceptionalPlaneResultants.lean`](../../QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean)
uses the parameter type
`HomogeneousMonomial 4 n ⊕ Fin 4`. Its first group consists of every
degree-`n` coefficient of `G`; its second consists of the four normal
coordinates. The actual generic form and normal are polynomials in these
independent parameters. For fixed `A,n`, the proved parameter substitution
for Lang elimination supplies a single finite family

\[
 R_j\in\mathbb Z[\mathbf g,u_1,u_2,u_3,u_4].
\]

The quantifiers in `exceptionalPlane_resultants_over_fields` select this
family before the coefficient field, `G`, and the normal. Its simultaneous
zeros detect the nonzero geometric zeros of the literal second system.
`exceptionalPlane_resultant_family` states the same fact as failure of
geometric rank three.

The definition `specializePlaneResultant G (R j)` substitutes the actual
coefficients of `G` and leaves the four normal coordinates as variables.
The identity `eval_specializePlaneResultant` proves that evaluating this
partly specialized polynomial equals evaluating the original joint
parameter polynomial. No polynomial depending on `G` is chosen before
the uniform family or its degree bound has been fixed.

## Part (ii): the geometric plane witness and descent of nonvanishing

The new geometric literature premise is
`Trusted.bertini_homogeneous_tangent`. Its source boundary is explicitly
composite: Hartshorne's Bertini theorem and the general projective
Jacobian, dimension, component and tangent-space interpretation reviewed
in [bertini_input.md](bertini_input.md). It concerns arbitrary homogeneous
systems and projective dimensions. It supplies a hyperplane functional
nonzero on a common tangent vector, and contains no `D_p`, resultant,
degree estimate, or manuscript-specific rank-three conclusion.

[`BertiniPlane.lean`](../../QuaternaryQuadraticForms/BertiniPlane.lean)
specializes it internally to the two actual equations. It verifies their
homogeneity, positive degrees and literal rank-two hypothesis. The
elementary theorem `rank_three_of_rank_two_of_tangent` then shows that the
normal lies outside the span of the two gradients, hence gives rank three.
This produces a transverse normal `u₀` over the algebraic closure.

[`PlaneResultantSpecialization.lean`](../../QuaternaryQuadraticForms/PlaneResultantSpecialization.lean)
proves two needed algebraic bridges. First, over an algebraically closed
field, `HasNonzeroGeometricZero` is equivalent to existence of a nonzero
common zero in that same field. This is proved using bijectivity of its
map into its algebraic closure, including transport of the nonzero vector
and all polynomial evaluations. Thus no extra assumption is made about a
second algebraic closure. Second, partial specialization of `R_j` commutes
with every coefficient homomorphism.

Apply the fixed resultant family over the algebraic closure at `u₀`.
Since this plane is transverse, not every resultant value can vanish.
Choose an index `j` with nonzero value. If the base-field polynomial
`S = specializePlaneResultant G (R j)` were zero, its coefficient extension
would be zero, and its evaluation at `u₀` would vanish. The proved map
identity contradicts the chosen nonzero resultant value. Hence `S ≠ 0`
as a polynomial over the base field.

The chosen normal is not required to be rational over the base field.
Nor does this argument infer a polynomial identity from values on a
finite field. The result asserts nonvanishing of a polynomial, not
existence of a prime-field normal outside its zero set; the latter is
not a clause of Lemma 4.1(ii).

## Part (ii): the degree bound and final polynomial

The code fixes

\[
 E=2+\max_j\deg R_j
\]

immediately after selecting the integral family. The maximum is over the
joint parameter polynomials and is represented by a finite supremum, with
value zero if the family is empty. Thus `E ≥ 2`, and it depends only on
`A,n`. For admissible data the transverse witness produces an actual
index, so an empty family cannot occur in that application.

[`ParameterSpecialization.lean`](../../QuaternaryQuadraticForms/ParameterSpecialization.lean)
proves that substitution by polynomials of degree at most one cannot
increase total degree. The form coefficients are substituted by constants
and the normal coordinates by degree-one variables. Therefore
`totalDegree_specializePlaneResultant_le` in
[`ExceptionalPlaneDegree.lean`](../../QuaternaryQuadraticForms/ExceptionalPlaneDegree.lean)
gives `deg S ≤ deg R_j`. Using total degree in all joint parameters may
give a larger bound than using only the normal variables; it still gives
the required uniform degree bound.

The final polynomial is the literal product

\[
 D(u)=F^*(u)S(u),\qquad
 F^*(u)=u^{\mathsf T}\operatorname{adj}(A_K)u.
\]

Here `A_K` is the coefficient image of the fixed integral matrix. The
adjugate is symmetric and nonsingular; its determinant is a positive
power of the nonzero determinant of `A_K`. With two nonzero in the field,
the actual quadratic polynomial associated to that adjugate is nonzero.
Since the polynomial ring over a field is a domain and `S ≠ 0`, the
product is nonzero. Its degree is at most `2 + deg R_j ≤ E`, and its value
at the origin is zero because the quadratic factor vanishes there.

If `D(u) ≠ 0`, each factor has nonzero value. The first gives the exact
dual-form condition. If geometric transversality failed, the second
elimination system would have a nonzero geometric common zero, so every
specialized resultant, including `S`, would vanish at `u`. This contradicts
the other factor. The conclusion therefore quantifies over all nonzero
common zeros in the algebraic closure, as in equation (4.2).

The final prime-field wrapper first obtains finiteness from the proved
part (i). It then applies `not_dvd_polynomialBadPrimeModulus_iff` to the
literal `p ∤ N_G` hypothesis. This supplies both good reduction and
`p ∤ N_F`, from which odd characteristic and nonsingularity of the reduced
matrix follow. All hypotheses of the field-level construction are thus
deduced from the source assumptions. In particular no condition
`p ∤ n` is introduced.

## Complete Lemma 4.1: correspondence conclusion

The final exports for parts (i) and (ii) cover every source clause under
the source hypotheses. Their constants are chosen for the same fixed
`A,n` before the varying form, and can therefore be taken together as the
constants in the single two-part lemma. No additional geometric, arithmetic,
or coefficient-dependent hypothesis is required.

The literature boundary for part (i) is Lang elimination. Part (ii) uses
that same registered general input and the separately reviewed composite
Bertini interface. The actual equations, rank interpretations, coefficient
maps, nonzero specialized resultant, uniform degree, dual quadratic,
and final exceptional polynomial are internal deductions.

The final module has passed the pinned strict Lean build. The full
repository verifier, inspected final theorem types and axiom dependencies,
recorded input hashes, and exact commit/run evidence remain separate
verification gates, recorded in the live ledger and execution checkpoint.
This source-correspondence review finds no omitted clause or strengthened
hypothesis and supports complete classification once those gates pass.
