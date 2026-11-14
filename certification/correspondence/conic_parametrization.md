# Lemma 4.2: the conic parametrization

## Frozen statement and exports

The source is `lem:conic` in
[the frozen manuscript](../../manuscript/quadratic_character_sums_github.tex).
The source hash and compiled numbering are recorded in
[source.json](../source.json). The complete statement is implemented by
`conic_parametrization` in
[ConicParametrization.lean](../../QuaternaryQuadraticForms/ConicParametrization.lean).
`conic_parametrization_prime_field` gives the corresponding finite-field
statement before the integral good-prime hypotheses are discharged.

The conclusion chooses one tuple of four binary quadratic polynomials over
`ZMod p` **before** quantifying over extension fields. For every field `L`
with an `Algebra (ZMod p) L` structure, coefficient extension of this same
tuple gives the required projective bijection and independent partial
derivatives. Thus the formal statement does not choose a new parametrization
for each extension, or merely prove the assertion over the algebraic closure.

## Hypothesis and object correspondence

| Manuscript item | Formal expression or deduction |
|---|---|
| Integral symmetric matrix A | `A : Matrix (Fin 4) (Fin 4) ℤ`, `A.transpose = A` |
| p is prime | `Fact p.Prime` |
| p does not divide N_F = 2\|det A\| | `¬ p ∣ quadraticBadPrimeModulus A`, where the modulus is `2 * A.det.natAbs` |
| Reduction of F modulo p | `matrixQuadraticPolynomial (reduceQuadraticMatrix p A)` |
| F*(u) is nonzero | `dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u) ≠ 0` |
| Binary quadratic coordinate forms | `μ : Fin 4 → MvPolynomial (Fin 2) (ZMod p)`, each `μ i` homogeneous of degree 2 |
| Projective plane section | `PlaneConicPoints A u`, the actual projective quotient restricted by the two equations |
| Bijection and differential condition | The constructed `ParametrizedPlaneSection` record over each extension |

[GoodPrime.lean](../../QuaternaryQuadraticForms/GoodPrime.lean) proves
`goodPrime_ne_two`, `goodPrime_reduced_det_ne_zero`, and
`reduceQuadraticMatrix_symmetric`. Its
`reduceQuadraticMatrix_adjugate` proves that reducing the integral adjugate
agrees with taking the adjugate after reduction. The dual-form hypothesis is
therefore the literal reduction of equation `eq:dualform`.

The manuscript's global assumption that the integral determinant is not a
square is unnecessary for this local lemma. It is not added as a formal
hypothesis. Good reduction and the nonzero dual value supply the local
nondegeneracy needed below.

## Construction and all clauses

### 1. A nondegenerate ternary space with an isotropic point

[QuadraticPlane.lean](../../QuaternaryQuadraticForms/QuadraticPlane.lean)
defines `planeSubspace u` as the kernel of the actual dot-product functional.
The adjugate identity identifies its orthogonal normal and proves
`plane_bilin_nondegenerate`; `planeSubspace_finrank` proves dimension three.

`plane_exists_isotropic` applies the official mathlib Chevalley–Warning
theorem to the quadratic and linear equations in four variables: their total
degrees sum to at most three. The number of common affine zeros is divisible
by p. If the origin were the only zero, p would divide one, a contradiction.
This is a proved replacement for the manuscript's intersection of two
value sets. Existence of an isotropic point is not assumed or registered as
a literature premise.

`plane_exists_hyperbolic_coordinates` in
[ConicNormalForm.lean](../../QuaternaryQuadraticForms/ConicNormalForm.lean)
constructs a linear coordinate equivalence and a nonzero coefficient a for
which the restricted form is `y₀*y₁ + a*y₂²`. It proves this normal form from
nondegeneracy, the isotropic point, and odd characteristic.

### 2. Literal projective maps and literal derivatives

[ConicCharts.lean](../../QuaternaryQuadraticForms/ConicCharts.lean) uses the
explicit vector `(-a*s², t², s*t)`. It proves nonvanishing away from the
origin, compatibility with scaling, and injectivity and surjectivity on
mathlib's projective quotient. `canonicalConicEquiv` is consequently an
actual equivalence of projective point types.

[ConicPolynomials.lean](../../QuaternaryQuadraticForms/ConicPolynomials.lean)
implements these coordinates as multivariate polynomials. Their evaluated
formal partial derivatives are `(-2*a*s, 0, t)` and `(0, 2*t, s)`;
`canonicalConicPolynomials_partials_independent` proves independence for
every nonzero `(s,t)` when a and 2 are nonzero.

[EmbeddedConic.lean](../../QuaternaryQuadraticForms/EmbeddedConic.lean)
transports these constructions through the injective coordinate map into
four-space. `embeddedConicEquiv_mk` identifies the equivalence on every
representative with evaluation of the actual coordinate polynomials, and
`embeddedConicPolynomials_partials_independent` proves independence of
their actual `MvPolynomial.pderiv` evaluations.

### 3. Extension fields and polynomial identities

The passage from finite-field evaluations to arbitrary extensions uses
polynomial identities. `coordinateQuadratic_pullback` and
`extendCoordinateMap_quadratic` first prove equality of homogeneous
quadratic polynomials, using mathlib's `IsHomogeneous.funext_of_le_card`
with degree 2 at most the cardinality of the field. The corresponding plane
identity has degree 1. They then map coefficients and evaluate over the
extension. No unrestricted inference from equality of finite-field
functions to equality of polynomials is used.

[ScalarExtension.lean](../../QuaternaryQuadraticForms/ScalarExtension.lean)
also proves that the extended coordinate map remains injective and its range
is exactly the extended hyperplane. `embeddedConicPolynomials_map` identifies
the new coordinates with coefficient extension of the original tuple.

`embeddedParametrizedPlaneSection` constructs the record defined in
[PlaneConic.lean](../../QuaternaryQuadraticForms/PlaneConic.lean): homogeneous
coordinates, nonzero values, a projective equivalence with its exact
representative formula, independent partials, and the polynomial identities
`F ∘ μ = 0` and `(u·) ∘ μ = 0`. These are proved fields of the constructed
record, not additional assumptions in `conic_parametrization`.

## Trust and verification scope

Every ingredient of this lemma is proved from Lean's standard foundations
and the pinned official mathlib. No external mathematical premise is added;
in particular, neither conic parametrizability nor Chevalley–Warning is an
unproved axiom in this project.

This record covers both clauses of the frozen lemma, including the common
choice over all extensions. Repository-wide execution evidence is recorded separately in
[CHECKPOINT.md](../../CHECKPOINT.md) and the verification reports. This
correspondence review does not by itself replace those checks.
