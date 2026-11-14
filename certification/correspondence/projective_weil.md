# Corollary 2.6: the projective-line character sum

## Frozen statement and checked export

The source is `cor:weilline`, equation `eq:weilline`, in
[the frozen manuscript](../../manuscript/quadratic_character_sums_github.tex).
The complete statement is implemented by `projective_weil_bound` in
[ProjectiveWeil.lean](../../QuaternaryQuadraticForms/ProjectiveWeil.lean).

The only additional trusted mathematical input is
`QuaternaryQuadraticForms.Trusted.weil_simple_roots`, registered as `EXT.WEIL`.
The [separate input review](weil_input.md) records its exact source and scope.
No projective geometry or polynomial hypothesis is part of that premise.

## Hypothesis correspondence

| Manuscript hypothesis | Formal expression |
|---|---|
| p is prime | `Fact p.Prime`; the field is `ZMod p` |
| ψ is nonprincipal | `ψ : MulChar (ZMod p) ℂ` and `ψ ≠ 1` |
| ψⁿ is principal | `ψ ^ n = 1` |
| n ≥ 2 | `2 ≤ n` |
| g is a binary form of degree n | `g : MvPolynomial (Fin 2) (ZMod p)`, `g.IsHomogeneous n`, and `g ≠ 0` |
| g has n distinct zeros in the projective line over the algebraic closure | `Nat.card (geometricBinaryProjectiveZeros g) = n` |

Homogeneity alone would admit the zero polynomial. The explicit nonzero
condition excludes it and, together with homogeneity, implies actual total
degree n by mathlib's `MvPolynomial.IsHomogeneous.totalDegree`.

`geometricBinaryProjectiveZeros g` is the set of points of mathlib's actual
projectivization of `Fin 2 → AlgebraicClosure (ZMod p)` where the coefficient
extension of g vanishes. It does not require the geometric zeros to be rational
over the prime field. The zero set counts distinct points, not multiplicities.
Its zero condition is proved invariant under multiplication by field units.

The chart equivalence proves that this zero set corresponds to a finite
polynomial root set and, possibly, one point at infinity. The use of `Nat.card`
therefore has no infinite-set ambiguity. Nonvanishing of g also ensures that
the affine polynomial is nonzero before mathlib's root-set convention is used.

## The checked deductions

### 1. Actual projective charts and invariant weights

[ProjectiveLine.lean](../../QuaternaryQuadraticForms/ProjectiveLine.lean)
constructs a bijection between `Option K` and the actual projective line.
`none` represents `(1:0)` and `some z` represents `(z:1)`. Its injectivity
and surjectivity are proved using the quotient's nonzero-scalar equivalence.

The previously checked `polynomialCharacterWeight_units_smul` applies in
two coordinates. Homogeneity and `ψ ^ n = 1` prove independence of the chosen
representative. The theorem `projectiveLineCharacterSum_chart` consequently
identifies the literal projective sum with

    ψ(g(1,0)) + sum_{z in F_p} ψ(g(z,1)).

### 2. Literal polynomial substitution and its degree

[BinaryForms.lean](../../QuaternaryQuadraticForms/BinaryForms.lean) defines
`binaryDehom g` as the substitution of `Polynomial.X` and `1` into g.
It proves evaluation compatibility and compatibility with coefficient
extension. Homogenizing again to degree n recovers g. This proves that the
affine polynomial is nonzero, and its degree is at most n.

The coefficient of degree n is exactly `g(1,0)`. Thus the affine degree is n
when infinity is not a zero, and is strictly smaller than n when it is.

### 3. Deriving the degree drop and the simple-root condition

[BinaryFormRoots.lean](../../QuaternaryQuadraticForms/BinaryFormRoots.lean)
uses the chart equivalence to prove the exact identity

    number of projective zeros
      = number of distinct affine roots + indicator(g(1,0)=0).

The cardinality of a polynomial's distinct root set cannot exceed its degree.
If infinity is a zero, the hypothesis supplies n−1 affine roots, while the
affine degree is strictly below n. Hence the degree and root count are both
n−1. If infinity is not a zero, the degree and root count are both n.
Since n≥2, both cases have positive degree.

This counting proof replaces the manuscript's intermediate discussion of
divisibility by t and nondivisibility by t². Those two divisibility statements
are not separately claimed as checked exports. The precise degree and root
conclusions needed for the corollary are proved.

The argument is applied after injective extension of coefficients to the
algebraic closure. Degree preservation and root-set compatibility then give
`binaryDehom_geometric_data`: positive degree, the degree bound, and as many
distinct geometric affine roots as the affine degree. Separability is also
proved explicitly in `binaryDehom_geometric_separable`.

### 4. Applying the univariate input and adding infinity

The proved affine data supply every hypothesis of Lemma 2.5. The norm of the
affine character sum is at most `(d−1)√p`, where d is the actual affine degree.
The character value at infinity has norm at most one, by the official
character library. The triangle inequality and d≤n give

    norm(projectiveLineCharacterSum p ψ g) ≤ (n−1)√p + 1.

All numerical operations on this right side are in the real numbers. The
finite sum, character evaluations, homogeneous polynomial, projective
quotient, and geometric root set in this proof are the actual mathematical
objects in the frozen statement.

## Review and scope

The source correspondence and counting argument were independently reviewed
against the frozen Corollary 2.6. The review found no extra manuscript
hypothesis and no internal deduction included in the trusted input.

The geometric and algebraic supporting exports use only Lean's standard
foundations. The final character-sum bound additionally depends on the single
registered Weil premise. The verification report prints the actual types and
axiom dependencies of both kinds of declarations separately.

This completes Corollary 2.6 relative to the accepted literature input. It
does not complete the conic parametrization, the plane-section estimate, or
the separate Katz estimate on the quadric.
