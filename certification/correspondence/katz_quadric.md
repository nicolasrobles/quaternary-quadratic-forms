# Source correspondence: Lemma 2.7

## Manuscript and checked statement

The source is the frozen manuscript
`manuscript/quadratic_character_sums_github.tex`, SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`:
Lemma 2.7 (`lem:katz`), hypothesis (2.13) (`eq:smoothp`), and conclusion
(2.14) (`eq:katz`). The principal export is
`QuaternaryQuadraticForms.katz_quadric_bound` in
[`KatzBound.lean`](../../QuaternaryQuadraticForms/KatzBound.lean).

For the actual integral symmetric matrix `A`, the export assumes a prime
`p` with `p ∤ 2 |det A|`, a nonprincipal multiplicative character `ψ`
modulo `p`, a homogeneous polynomial `G` of degree `n ≥ 2`, the equality
`ψ ^ n = 1`, and the manuscript's rank-two condition at every nonzero
common zero over the algebraic closure. Its conclusion is exactly

\[
 \left|\sum_{P\in\mathcal Q(\mathbb F_p)}\psi(G(P))\right|
 \le (2n^2-4n+4)p.
\]

The export has no separate smoothness, irreducibility, nonemptiness,
nonzero-polynomial, or Chern-coefficient assumption. These are supplied by
the internal deductions described below. It also imposes no restriction
`p ∤ n` or exact-order condition on the character.

## Correspondence of the objects and hypotheses

| Manuscript object or hypothesis | Lean realization and correspondence |
| --- | --- |
| `F(x) = xᵀ A x` | `matrixQuadraticPolynomial A` is the double sum of the actual matrix coefficients times coordinate monomials. `eval_matrixQuadraticPolynomial` proves that its evaluation is `dotProduct x (A.mulVec x)`. |
| `N_F = 2 |det A|` | `quadraticBadPrimeModulus A = 2 * A.det.natAbs`. `reduceQuadraticMatrix p A` reduces the entries of this same integral matrix. |
| `p ∤ N_F` | `goodPrime_ne_two`, `goodPrime_reduced_det_ne_zero`, and `reduceQuadraticMatrix_symmetric` supply odd characteristic, an invertible reduced matrix, and symmetry. |
| Form of degree `n` | `G.IsHomogeneous n`, together with the internally proved `G ≠ 0`, gives the intended nonzero form of that degree. |
| Nonprincipal character, `ψⁿ` principal | `ψ : MulChar (ZMod p) ℂ`, `ψ ≠ 1`, and `ψ ^ n = 1`. Here `1` is the principal multiplicative character. |
| Equation (2.13) | `ProjectiveIntersectionTransverseRank` uses the rank of the matrix with the two actual formal gradients as rows. Both polynomials are mapped to `AlgebraicClosure (ZMod p)`, and the predicate quantifies over all nonzero geometric common zeros. |
| `𝒬(𝔽_p)` and its character sum | `PrimeProjective p` is the projectivization of `Fin 4 → ZMod p`. `projectiveQuadric` filters its actual points by `xᵀ A x = 0`; `projectiveTrace` sums `ψ (MvPolynomial.eval P.rep G)` over this set. |

The chosen projective representatives cause no change in the summand.
`polynomialCharacterWeight_units_smul` and `projectiveWeight_rep_mk` prove
representative independence from homogeneity and `ψ ^ n = 1`.
`mem_projectiveQuadric_mk` proves independence for the quadric equation.
The generic literature sum is tied to these same objects by
`projectiveHypersurfacePoints_matrix` and
`projectiveHypersurfaceTrace_matrix` in
[`ProjectiveSurfaceTrace.lean`](../../QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean).
There is no unidentified numerical variable standing in for the sum.

## Geometric deductions made internally

[`QuadricSmooth.lean`](../../QuaternaryQuadraticForms/QuadricSmooth.lean)
calculates the formal gradient of the literal polynomial. Symmetry gives
`∇F(x) = 2 A x`. Since the reduced determinant and `2` are nonzero, this
gradient cannot vanish at a nonzero vector. The calculation is transported
along any field embedding, giving
`matrixQuadratic_projective_smooth_map` over the algebraic closure.
Thus the literature input receives the required geometric predicate, not
merely nonsingularity at prime-field points.

The same module proves `matrixQuadraticPolynomial_irreducible_map`.
First the polynomial is nonzero and has total degree exactly two. A
factorization into nonunits would therefore consist of two polynomials
of degree one. Their gradients are constant. The product rule would force
the entire gradient image of `F` into the span of those two constant
vectors. A nonzero vector annihilating that span would annihilate the
matrix bilinear form against every vector, contradicting its
nondegeneracy. This argument holds over every extension field, so it
establishes the actual geometric irreducibility required by the source.
It is a different elementary proof of the same fact used in the manuscript.

The final export does not assume `G ≠ 0`.
`quadric_transverse_polynomial_ne_zero` proves it: the existing
`plane_exists_isotropic` theorem, using mathlib's Chevalley–Warning theorem,
provides a nonzero quadric point. It remains nonzero after extension to the
algebraic closure. If `G` were zero, its gradient would be zero at this
point, contradicting the assumed rank two. This closes the potential
vacuity in a homogeneous-polynomial hypothesis, since the zero polynomial
is homogeneous of every degree.

The definitions of the two-gradient predicate and its equivalence with
linear independence are in
[`GoodReduction.lean`](../../QuaternaryQuadraticForms/GoodReduction.lean).
The rank condition is retained exactly as a hypothesis of Lemma 2.7;
it is not replaced by prime-field-only transversality or an unnamed
geometric property.

## The source-relative boundary

The only new literature premise used for this estimate is
`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data` in
[`Trusted/Katz.lean`](../../QuaternaryQuadraticForms/Trusted/Katz.lean).
It is the explicitly composite interface documented in
[`katz_input.md`](katz_input.md), registered against `EXT.KATZ` and
`EXT.HYPERSURFACE_CHERN`.

For arbitrary smooth geometrically irreducible hypersurfaces of positive
degree `m` in projective three-space and transverse sections of positive
degree `n`, it supplies finite complex spectral data for the actual
projective character sum. The data have norm `p` and their number is the
unevaluated general Chern coefficient. This combines Katz's concentration,
purity, and trace formula with general hypersurface adjunction and the
degree identity `∫_X L² = m`. The interpretation of the actual homogeneous
polynomial and Jacobian predicates as the scheme hypotheses is included
explicitly in that general literature boundary.

This is a source-relative certificate: the repository does not formalize
étale cohomology or Chern classes. It does prove the manuscript's quadric
specialization and its scalar estimate from that registered general input.
In particular, the premise contains neither `m = 2`, the constant
`2n² − 4n + 4`, nor the desired scalar norm inequality. There is no
characteristic restriction on `m` or `n` hidden in the premise. The
restriction `p ≠ 2` in the quadric application is deduced from `p ∤ N_F`.

## Coefficient and norm deductions

[`SurfaceChern.lean`](../../QuaternaryQuadraticForms/SurfaceChern.lean)
works with integer polynomials. `SurfaceChernRelation m c` is the precise
coefficient relation

\[
 [T^j]\big((1+mT)c(T)\big)=[T^j](1+T)^4\qquad(0\le j\le2).
\]

The file proves that the relevant coefficients of `c` are
`1`, `4 − m`, and `m² − 4m + 6`. It verifies the relation for the quadric
polynomial `1 + 2T + 2T²`, and computes

\[
 2[T^2]\big((1+2T+2T^2)(1-nT+n^2T^2)\big)
 =2n^2-4n+4.
\]

All subtraction in these coefficient formulas occurs in `ℤ`; there is no
truncated natural-number subtraction. The dimension `r : ℕ` furnished by
the source input is equated with this integer coefficient. The wrapper
transports the resulting identity to `ℝ` with `exact_mod_cast` and applies
the internally proved `norm_sum_le_card_mul`. Thus

\[
 \left|\sum_{i<r}\lambda_i\right|
 \le\sum_{i<r}|\lambda_i|=rp=(2n^2-4n+4)p.
\]

## Scope comparison

The final export has the full conclusion and all material local hypotheses
of Lemma 2.7. The manuscript's standing assumption that `det A` is not a
square is unnecessary for this lemma and is omitted from the export.
Nonsingular split and nonsplit quadrics satisfy the same argument.
Likewise, a separate integral hypothesis `det A ≠ 0` is unnecessary in the
export because `p ∤ 2 |det A|` already excludes zero determinant. These
omissions strengthen the statement and do not restrict its applicability
to the frozen manuscript.

This correspondence record concerns statement fidelity and the proof
boundary. Build results, axiom reports, checked commits, and execution
status are recorded separately in the checkpoint and verification records.
