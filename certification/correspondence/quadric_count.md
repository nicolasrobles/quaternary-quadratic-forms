# Source correspondence: Lemma 2.3

## Scope and frozen source

This review covers `lem:quadriccount`, Lemma 2.3 and equation (2.7), including
its proof at lines 769–812 of
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex).
The frozen source SHA-256 is
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`;
the source file matches that hash. No manuscript revision is required.

| Source lines | Reviewed obligation |
| --- | --- |
| 769–776 | Rational symmetric nonsingular matrix, nonsquare determinant, and the actual integer zero count |
| 779–789 | Anisotropic case; normalized hyperbolic pair and two-dimensional orthogonal complement |
| 790–797 | Exact rational normal form, determinant/discriminant identity, and binary anisotropy |
| 799–806 | Positive common denominator, injective integer transformation, and transformed equation |
| 807–812 | Nonzero signed-divisor fibres, zero binary fibre, and the final power estimate |

## Exact endpoint and quantifiers

The complete source endpoint is `QuaternaryQuadraticForms.source_quadric_count`
in [QuadricCountingTheorem.lean](../../QuaternaryQuadraticForms/QuadricCountingTheorem.lean):

```lean
theorem source_quadric_count
    (S : Matrix (Fin 4) (Fin 4) ℚ) (hS : S.transpose = S)
    (hdet : S.det ≠ 0) (hns : ¬ IsSquare S.det)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      (sourceQuadricZeroSet S U).Finite ∧
      ((sourceQuadricZeroSet S U).ncard : ℝ) ≤ C * U ^ (2 + ε)
```

The constant is chosen after the rational form and positive epsilon, before
every real radius `U ≥ 1`. It therefore has precisely the permitted dependence
on `J` and epsilon. No uniformity in the coefficients of `S` is asserted.
The source's implicit positive-epsilon convention is an explicit hypothesis.
Finiteness is proved alongside the bound, so `Set.ncard` counts a finite set.

## Literal objects and representations

| Manuscript object | Lean representation |
| --- | --- |
| Rational symmetric matrix `S` | `Matrix (Fin 4) (Fin 4) ℚ` with `S.transpose = S` |
| Nonsingularity and nonsquare determinant | `S.det ≠ 0` and `¬ IsSquare S.det`, over the rationals |
| Integer vector `z` | `Fin 4 → ℤ`, with coordinatewise rational casts for evaluation |
| `J(z) = zᵀSz` | `rationalIntegerQuadricValue S z`, the literal dot product with `S.mulVec` |
| Euclidean norm | `integerEuclideanNorm`, the standard `EuclideanSpace ℝ (Fin 4)` norm of the real coordinate casts |
| Counted source set | `sourceQuadricZeroSet S U = {z : Fin 4 → ℤ \| integerEuclideanNorm z ≤ U ∧ rationalIntegerQuadricValue S z = 0}` |
| Finite representation | `integerQuadricZeros S U`, proved equal to the source set, with identical cardinality |

The origin is included. The radius is real, and no primitivity or projective
quotient is imposed. Lean coordinates `0,1,2,3` correspond to source coordinates
`1,2,3,4`. A coordinate box is used only as a finite representation or upper
bound; the final source set uses the actual Euclidean ball.

## Rational geometry and discriminant sign

If the rational form is anisotropic, every integer zero is the origin, giving
cardinality at most one. Otherwise nondegeneracy supplies a normalized
hyperbolic pair `e,f` with `J(e)=J(f)=0` and bilinear pairing `1/2`.
The common orthogonal complement has dimension two. Its basis together with
`e,f` is proved linearly independent, yielding a matrix `T` with nonzero determinant.

The matrix congruence gives `J(Ty)=y₀y₁+a y₂²+b y₂y₃+c y₃²` exactly.
The hyperbolic block has determinant `-1/4`, and the binary block has determinant
`ac-b²/4`; their product is `(b²-4ac)/16`. Thus the verified identity is
`det(S) det(T)² = (b²-4ac)/16`, with the positive discriminant sign in the source.
A nonzero rational binary zero forces square discriminant. Since `det(T) ≠ 0`,
this would make `det(S)` a rational square, contradicting the source hypothesis.
The argument applies also to negative determinants and assumes no positive definiteness.

## Denominators and transport of the lattice

`rational_family_clear_denominators` clears all entries of `T⁻¹` and all three
binary coefficients simultaneously using the localization at positive integers.
Its integer `k` satisfies `0 < k`, hence `k ≥ 1`. The construction sets
`L = k T⁻¹` entrywise and takes integral coefficients `a'=ka`, `b'=kb`, `c'=kc`.

For every integer `z`, the proof establishes the rational identity `T(Lz)=kz`.
This proves injectivity of `L.mulVec`; quadratic homogeneity then transfers
`J(z)=0` to `k y₀y₁+a' y₂²+b' y₂y₃+c' y₃²=0` for `y=Lz`.
The nonzero scalar also preserves binary anisotropy over the integers.
The transfer interface retains `k ≠ 0`, which is all the counting argument needs.

`integerMatrix_coordinate_bound` chooses a fixed `D ≥ 1` from the absolute
matrix entries and proves `|(Lz)ᵢ| ≤ D integerEuclideanNorm(z)` for every `z,i`.
The image of the source ball therefore lies in the coordinate box of radius `DU`.
Image cardinality equals source cardinality by injectivity. If the model count
has constant `C`, transport chooses `C D^(2+ε)` before quantifying over `U`.

## Signed divisors, zero fibre, and real radii

For nonzero binary value `n`, the first coordinate divides `n` and is nonzero.
The set `splitQuadricSignedDivisors n` explicitly includes both signs of each
positive divisor of `|n|`, giving at most `2 τ(|n|)` choices. For each choice,
the second coordinate is unique because `k y₀ ≠ 0`. No positive-sign assumption
on `n`, `k`, or the coordinates enters this argument.

The previously proved `divisors_card_le_rpow` is used with exponent `ε/2`.
The binary value satisfies `|n| ≤ A U²` for a fixed positive coefficient `A`,
so each nonzero fibre contributes at most a fixed multiple of `U^ε`.
The two binary coordinates lie in `[-⌊U⌋,⌊U⌋]`; for every real `U ≥ 1` this
interval has at most `3U` integers. Summing gives the required `U^(2+ε)` bound.

When the binary value vanishes, anisotropy forces both binary coordinates to
vanish. The remaining equation is `k y₀y₁=0`, so the points lie on two axes.
Their union has at most `6U` points, including the origin. This contribution
is absorbed using `U ≤ U^(2+ε)` for `U ≥ 1`. The two disjoint fibre cases cover
the complete model set, and all model constants precede the radius quantifier.

## New modules and public theorem exports

All names below are in `QuaternaryQuadraticForms`. The nine modules contain
28 public theorem exports; definitions are excluded from this count.

| Module in `QuaternaryQuadraticForms/` | Count | Public theorem exports |
| --- | ---: | --- |
| `QuadricCountingDefinitions.lean` | 6 | `mem_integerQuadricZeros`, `sourceQuadricZeroSet_eq`, `sourceQuadricZeroSet_finite`, `sourceQuadricZeroSet_ncard`, `integerQuadricZeros_card_le_one`, `integerQuadricZeros_bound_of_lattice_model` |
| `RationalQuadricGeometryAlgebra.lean` | 3 | `binary_zero_discriminant_isSquare`, `det_hyperbolic_binary`, `nonsquare_det_binary_anisotropic` |
| `RationalQuadricGeometryBasis.lean` | 3 | `exists_hyperbolic_complement_basis`, `rational_congruence_apply`, `exists_rational_hyperbolic_matrix` |
| `RationalQuadricNormalForm.lean` | 1 | `exists_rational_quadric_normal_form` |
| `RationalQuadricLattice.lean` | 3 | `rational_family_clear_denominators`, `integerMatrix_coordinate_bound`, `rationalQuadric_integer_model` |
| `SplitQuadricFibers.lean` | 3 | `splitQuadric_mem_signedDivisors`, `splitQuadric_signedDivisors_card_le`, `splitQuadric_nonzero_fiber_card_le` |
| `SplitQuadricBoxBounds.lean` | 4 | `splitQuadric_mem_interval`, `splitQuadricCoefficient_pos`, `splitQuadric_binaryValue_natAbs_le`, `splitQuadric_zero_fiber_card_le` |
| `SplitQuadricCounting.lean` | 3 | `splitQuadric_nonzero_fibers_uniform`, `splitQuadric_nonzero_box_card_le`, `splitQuadric_box_bound` |
| `QuadricCountingTheorem.lean` | 2 | `rationalQuadric_euclidean_bound`, `source_quadric_count` |

## Dependencies and boundary of the review

No new literature premise is introduced. The proof uses existing proved
Euclidean-lattice, hyperbolic-partner, and divisor-bound results together with
the pinned Lean/mathlib libraries. The reviewed interfaces require no internal
manuscript deduction as an external assumption.

The weighted dual-cone consequence `aux:conecount`, equation (2.9), remains
**Pending** and is explicitly outside this review's scope. Its adjugate
specialization and dyadic weighted summation are separate obligations.
Aggregate verification, CI, and exact checked-commit evidence are recorded
separately in `CHECKPOINT.md`; this correspondence review makes no such claim.
