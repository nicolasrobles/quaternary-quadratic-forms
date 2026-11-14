# Lemma 4.3: the transverse plane-section bound

## Frozen statement and exports

The source is v35, `lem:section`, equation `eq:section`, in
[the frozen manuscript](../../manuscript/quadratic_character_sums_github.tex).
The source hash and compiled numbering are recorded in
[source.json](../source.json). The full source statement is implemented by
`plane_section_bound` in
[PlaneSectionTheorem.lean](../../QuaternaryQuadraticForms/PlaneSectionTheorem.lean).
Its prime-field version is `plane_section_bound_prime_field`.

The conclusion is the norm bound for the actual projective section sum:

    ‖projectiveSectionTrace (reduceQuadraticMatrix p A) ψ G u‖
      ≤ (2 * (n : ℝ) - 1) * Real.sqrt p + 1.

The final theorem constructs the parametrization required by its proof. It
does not assume a parametrization, separability, or a geometric root count.

## Hypothesis correspondence

| Manuscript hypothesis | Formal expression |
|---|---|
| Integral symmetric A and good prime p | `A.transpose = A`, `Fact p.Prime`, and `¬ p ∣ quadraticBadPrimeModulus A` |
| F*(u) is nonzero | The dot product of u with the adjugate of the reduced A applied to u is nonzero |
| ψ is nonprincipal modulo p | `ψ : MulChar (ZMod p) ℂ`, `ψ ≠ 1` |
| ψⁿ is principal | `ψ ^ n = 1` |
| n ≥ 2 and G is a form of degree n | `2 ≤ n`, `G : MvPolynomial (Fin 4) (ZMod p)`, `G.IsHomogeneous n` |
| Equation `eq:transverse` over the algebraic closure | `PlaneTransverseRank` for the coefficient extensions of F, G, and u |

The good-prime and dual-form expressions have the literal integral meaning
documented in the [Lemma 4.2 correspondence](conic_parametrization.md).
The global nonsquare-determinant assumption is unnecessary here as well.

`PlaneTransverseRank` in
[TransversalityRank.lean](../../QuaternaryQuadraticForms/TransversalityRank.lean)
uses `Matrix.rank` of the three-row matrix whose rows are the evaluated
formal gradients of F and G and the vector u. It quantifies over every
nonzero geometric vector satisfying all three equations. The theorems
`rank_three_iff_linearIndependent` and `planeTransverseRank_iff` prove the
equivalence with the linear-independence formulation used in the proof.
Thus the source's rank condition has not been replaced by an extra premise.

Homogeneity allows the zero polynomial in Lean. No additional `G ≠ 0`
hypothesis is imposed: transversality will imply that the pulled-back
polynomial is nonzero, which also excludes zero G. Together with homogeneity,
this gives the required actual degree.

## The checked deductions

### 1. One parametrization over the base field and the algebraic closure

`conic_parametrization_prime_field` supplies a single tuple μ over `ZMod p`
and its proved `ParametrizedPlaneSection` over every extension. The final
proof specializes this construction to the prime field and its algebraic
closure. The base and geometric parametrizations are therefore coefficient
extensions of the same polynomials.

Set `g := MvPolynomial.aeval μ G`. Homogeneous polynomial substitution proves
that g is homogeneous of degree `2*n`. `map_aeval_polynomial` and
`matrixQuadraticPolynomial_map` in
[ScalarExtension.lean](../../QuaternaryQuadraticForms/ScalarExtension.lean)
identify its coefficient extension with the geometric pullback.

### 2. Transversality excludes singular zeros of the pullback

[PolynomialChainRule.lean](../../QuaternaryQuadraticForms/PolynomialChainRule.lean)
proves `pderiv_aeval_chain_rule` and its evaluated form for actual polynomial
substitution and formal partial differentiation.

`transverse_pullback_nonsingular` in
[TransversePullback.lean](../../QuaternaryQuadraticForms/TransversePullback.lean)
applies this chain rule to the proved polynomial identities `F ∘ μ = 0` and
`(u·) ∘ μ = 0`, and to G. If g and both its partials vanished at a nonzero
binary vector, its image x would be a nonzero common zero of F, G, and the
plane equation. All three gradient rows would annihilate the two independent
vectors `∂μ/∂s` and `∂μ/∂t`.

`independent_three_two_dot_impossible` proves the contradiction by identifying
dot products with covectors: three independent covectors in dimension four
have a one-dimensional common annihilator, which cannot contain two
independent vectors. The gradients, derivatives, nonzero image, and the
annihilator dimension are all established for the actual polynomial maps.

### 3. Nonsingularity gives exactly 2n distinct geometric projective zeros

[BinaryNonsingular.lean](../../QuaternaryQuadraticForms/BinaryNonsingular.lean)
proves `binary_nonsingular_geometric_roots`. Its hypothesis excludes a
nonzero common zero of a homogeneous binary polynomial and both partials;
its conclusion gives both nonvanishing of the polynomial and the literal
cardinality of its geometric projective zero set.

The proof uses `binaryDehom g = g(X,1)`. Formal differentiation commutes with
this substitution. Euler's identity

    s * ∂g/∂s + t * ∂g/∂t = degree(g) * g

shows that an affine repeated root would make both partials vanish. Hence
the affine polynomial is separable over the algebraic closure. At infinity,
if `g(1,0) = 0`, Euler's identity gives `∂g/∂s(1,0) = 0`, and nonsingularity
forces `∂g/∂t(1,0) ≠ 0`. Comparing coefficients proves that the affine degree
is exactly `2*n - 1`; otherwise it is `2*n`. The established projective-chart
count then gives exactly `2*n` distinct geometric points.

There is no division by the degree in this argument. In particular, no
assumption that p is coprime to n or to 2n is introduced. The root count is
derived, not assumed as a substitute for transversality.

### 4. Transporting the literal sum and applying Corollary 2.6

[PlaneSectionBound.lean](../../QuaternaryQuadraticForms/PlaneSectionBound.lean)
first proves `projectiveSectionTrace_eq_sum_conic`, identifying the filtered
sum over the actual quadric with the sum over its projective plane-section
subtype. `projectiveSectionTrace_eq_projectiveLine` then transports it along
the constructed equivalence. Its representative formula and the proved
invariance of the weight `ψ(G(P))`, using `ψ ^ n = 1`, give

    projectiveSectionTrace A ψ G u
      = projectiveLineCharacterSum p ψ (MvPolynomial.aeval μ G).

The character relation implies `ψ ^ (2*n) = 1`. The derived nonvanishing,
homogeneity, and geometric root count supply every polynomial hypothesis of
`projective_weil_bound`. Its bound is `(2*n - 1)√p + 1`, with the subtraction
and final inequality taken in the real numbers. This proves
`plane_section_bound_of_parametrization`; the final source theorem supplies
its parametrizations and rank-to-independence conversion internally.

## Trust and verification scope

The only external mathematical premise is the existing
`QuaternaryQuadraticForms.Trusted.weil_simple_roots`, registered as `EXT.WEIL`.
Its exact scope is reviewed in [weil_input.md](weil_input.md), and its
projective-line deduction in [projective_weil.md](projective_weil.md).
The conic construction, chain rule, rank argument, nonvanishing, root count,
and transport of sums introduce no further trusted input.

This record covers the complete frozen plane-section statement.
Repository-wide execution evidence is recorded separately in
[CHECKPOINT.md](../../CHECKPOINT.md) and the verification reports. This
correspondence review does not replace those checks or certify the
separate Katz estimate.
