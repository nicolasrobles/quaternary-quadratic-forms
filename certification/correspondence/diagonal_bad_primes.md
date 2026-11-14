# Source correspondence: Lemma 4.5

## Scope and frozen source

This review covers every clause of `lem:diagbad`, Lemma 4.5: characteristic-zero
smoothness of the diagonal pair, the exact criterion for bad reduction at
primes outside `N_F`, and the equality `N_G = rad(2 α M)` for the existing
bad-prime modulus. Finiteness of its defining product is proved internally.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Content |
| --- | --- |
| `eq:forms`, lines 157–164 | The integral symmetric nonsingular matrix, `F(x)=xᵀAx`, `α=det A`, and `N_F=2 abs(α)`; the standing nonsquare assumption |
| `eq:diagonal`, lines 205–208 | The two sums of four coefficient-weighted squares and all six nonzero differences `a_i b_j-a_j b_i` |
| `eq:smooth`, lines 283–287, and lines 290–294 | The actual rank-two condition over the relevant algebraic closure and the definition of good reduction |
| `eq:NG`, lines 295–299 | The radical of `N_F` times the product of the additional bad primes |
| `eq:kappadef`, lines 383–386 | The six-factor integer `M` |
| `lem:diagbad`, lines 1862–1866; proof at lines 1868–1882 | All three assertions and their diagonal gradient argument |

The subsection also defines `κ_i` and fixes a quadratic character. Neither
enters this lemma, whose assertions concern the forms, geometric rank, and
integer modulus.

## Modules and final statement

| Module | Reviewed role |
| --- | --- |
| [DiagonalForms.lean](../../QuaternaryQuadraticForms/DiagonalForms.lean) | Exact formal polynomial identity, the literal six-factor product, coefficient maps, nonvanishing, and the signed modulus conversion |
| [DiagonalGeometry.lean](../../QuaternaryQuadraticForms/DiagonalGeometry.lean) | Actual gradients and minors, rank two under nonzero pair differences, and the geometric rank-failure witness |
| [DiagonalReduction.lean](../../QuaternaryQuadraticForms/DiagonalReduction.lean) | Characteristic-zero smoothness and the literal primewise good/bad-reduction criterion |
| [BadPrimeRadical.lean](../../QuaternaryQuadraticForms/BadPrimeRadical.lean) | Direct finiteness and the exact radical identity from a geometric divisibility criterion |
| [DiagonalBadPrimes.lean](../../QuaternaryQuadraticForms/DiagonalBadPrimes.lean) | Specialization of the arithmetic to `M` and the complete Lemma 4.5 export |

The final declaration is `QuaternaryQuadraticForms.diagonal_bad_primes`.
Its data are `a b : Fin 4 → ℤ`; its only coefficient assumptions are

```lean
(∏ i, a i) ≠ 0
∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0
```

Its three conjuncts are exactly the following source clauses.

| Source assertion | Final Lean conclusion |
| --- | --- |
| `G` satisfies characteristic-zero smoothness | `SmoothCharacteristicZero (Matrix.diagonal a) (matrixQuadraticPolynomial (Matrix.diagonal b))` |
| At every prime `p ∤ N_F`, bad reduction is equivalent to `p ∣ M` | The negation of the actual `GoodReductionAt`, equivalent to `(p : ℤ) ∣ diagonalPairProduct a b`, under `[Fact p.Prime]` and nondivisibility of `quadraticBadPrimeModulus (Matrix.diagonal a)` |
| `N_G = rad(2 α M)` | Equality of the existing `polynomialBadPrimeModulus` with `primeRadical (2 * (∏ i, a i) * diagonalPairProduct a b).natAbs`, using the internally proved finiteness argument |

For a diagonal matrix, `Matrix.det_diagonal` identifies the determinant
with `∏ i, a i`. The first assumption therefore expresses the source's
nonsingularity, and `diagonal_coefficients_ne_zero` derives each `a_i ≠ 0`.
Symmetry is automatic for a diagonal matrix. The standing nonsquare
determinant assumption is unnecessary for this lemma; omitting it gives
a broader theorem without excluding any source instance.

There is no assumption that the `b_i` are nonzero, that any coefficient or
product is positive, that `M` is squarefree, or that `N_F` and `M` are
coprime. The six differences and the first coefficient product are the
precise source hypotheses used.

## Literal polynomials, pair product, and coefficient maps

`diagonalQuadraticPolynomial_eq_sum` proves, over every commutative ring,
the identity of formal multivariate polynomials

$$
\operatorname{matrixQuadraticPolynomial}(\operatorname{diag}(a))
 =\sum_i a_iX_i^2.
$$

Thus the definitions used in the final theorem are the actual two source
polynomials. This is a polynomial identity, not just agreement of their
evaluation functions on a finite field.

The definition `diagonalPairProduct` is

```lean
∏ i : Fin 4, ∏ j ∈ Finset.univ.filter (fun j => i < j),
  (a i * b j - a j * b i)
```

There are exactly six factors: `(0,1)`, `(0,2)`, `(0,3)`, `(1,2)`, `(1,3)`,
and `(2,3)`. Relabeling these indices by `1,2,3,4` gives the source's `M`,
with the same orientation of every difference. It is not a product over
all ordered distinct pairs and does not replace `M` by its square.

`diagonalPairProduct_ne_zero_iff` proves that `M ≠ 0` is equivalent to
nonvanishing of all six factors over a nontrivial integral domain.
`diagonal_pair_difference_ne_zero` extends that condition to every
distinct ordered pair by changing the sign when the order is reversed.

`diagonalPairProduct_map` commutes the exact product with a coefficient
homomorphism. `diagonalQuadraticPolynomial_map` does the same for the
formal diagonal polynomial. These identities account for both reduction
of integer coefficients modulo a prime and their subsequent extension
to an algebraic closure.

## The diagonal geometric argument

The geometric proof uses literal polynomial evaluation, formal gradients,
and `Matrix.rank`. The preceding `RankMinors.lean` equivalence between
rank failure and vanishing minors is applied to these actual rows.

`eval_diagonalQuadraticPolynomial` gives the source evaluation formula.
`polynomialGradient_diagonalQuadraticPolynomial` proves that the gradient
has coordinates `2 * a i * x i`. Consequently `diagonal_gradient_minor`
proves the exact identity

$$
\partial_iF(x)\partial_jG(x)-\partial_jF(x)\partial_iG(x)
 =4x_ix_j(a_ib_j-a_jb_i).
$$

### Nonzero pair differences give rank two

`diagonal_projectiveIntersectionTransverseRank` works over any field
where two is nonzero and every `a_i` and distinct pair difference is
nonzero. The condition on two includes characteristic zero as well as
positive characteristic different from two.

Suppose a nonzero common zero had rank different from two. All its
two-by-two minors would vanish. The displayed identity, the nonzero
factor four, and the nonzero pair differences force `x_i x_j = 0` for
every distinct pair. Choose a nonzero coordinate `x_i`; all other
coordinates vanish. The actual value of `F` is then `a_i x_i² ≠ 0`,
contradicting the common-zero hypothesis. This proves the required rank
condition. It does not assume smoothness as a separate geometric premise.

### A vanishing pair difference gives a geometric witness

`exists_diagonal_rank_failure_of_pair_eq_zero` assumes an algebraically
closed coefficient field, nonzero first-form coefficients, distinct
indices `i,j`, and a vanishing pair difference. The proved library result
`IsAlgClosed.exists_pow_nat_eq` supplies a square root `z` satisfying

$$
z^2=-a_i/a_j.
$$

The vector is the literal `Pi.single i 1 + Pi.single j z`. Its `i`th
coordinate is one, so it is nonzero. Direct evaluation gives `F(x)=0`;
the vanishing pair difference gives `G(x)=0`. The proof then verifies
the identity of gradient vectors

$$
\nabla G(x)=(b_i/a_i)\nabla F(x).
$$

All gradient minors therefore vanish, and the actual matrix has rank
different from two. This is the source's bad-reduction point, with
proportional rows giving the final rank-failure calculation. The argument
allows `b_i=0`: the scalar of proportionality may be zero.

The witness is constructed over the algebraically closed field. No square
root in the prime field, or rational singular point, is assumed.
`diagonal_projectiveIntersectionTransverseRank_iff` combines the two
directions. The pair-product version in `DiagonalReduction.lean` then
identifies this rank condition with nonvanishing of the actual six-factor
product.

## Characteristic zero and the exact prime range

`diagonal_smooth_characteristicZero` maps the two integral polynomials
into `AlgebraicClosure ℚ`, exactly as in the definition of
`SmoothCharacteristicZero`. Integer casts preserve the nonzero first
coefficients and pair differences, and two is nonzero. The proved field
criterion supplies the first clause of Lemma 4.5.

For a prime `p ∤ N_F`, `diagonal_badReductionAt_iff` uses the existing
quadratic modulus. Nondivisibility gives two nonzero in `ZMod p` and a
nonzero determinant for the reduced matrix. For the diagonal matrix this
gives every reduced `a_i ≠ 0`. The map from `ZMod p` into its algebraic
closure is injective, so these properties persist after scalar extension.

The maps of both actual polynomials are rewritten using the proved
coefficient-map identities. The geometric criterion says that good
reduction is equivalent to nonvanishing of the image of `M`. Injectivity
of the field extension and `ZMod.intCast_zmod_eq_zero_iff_dvd` identify
vanishing with the literal integer divisibility `(p : ℤ) ∣ M`.
Negating this equivalence gives the asserted criterion for bad reduction.

The primewise equivalence requires only primality and `p ∤ N_F`; it
does not additionally assume that the integral `M` is nonzero. In
particular it remains valid when `M=0`, as a stronger intermediate result.
The final source theorem uses the six nonzero integer differences, which
do give `M ≠ 0` for its finiteness and modulus conclusions.

The exact source range is retained. The criterion makes no assertion
about good or bad reduction at primes dividing `N_F`. The prime `3` is
not excluded when it lies outside `N_F`. The later observation in the
manuscript that `p ∤ 2 α M` implies `p ≥ 5` is not an added hypothesis
of Lemma 4.5 or its formalization.

## Direct finiteness and the existing modulus

The arithmetic helper `badReductionPrimes_finite_of_iff_dvd` takes a
fixed nonzero integer `z` and the proved criterion for the actual
`GoodReductionAt` predicate. Every additional bad prime divides `z`,
so the existing theorem about divisors of a nonzero integer proves
finiteness of the actual bad-prime set. Applying this with `z=M` gives
`diagonal_badReductionPrimes_finite`.

This finiteness proof is direct. It uses neither a new finite set as a
replacement definition nor the general elimination-based finiteness
theorem. In the final `diagonal_bad_primes` statement, it supplies the
proof argument required by the existing `polynomialBadPrimeModulus`.

The exact equality is established at the level of finite sets and
products. For any proof `hfinite` of the same set's finiteness,
`badReductionPrimes_toFinset_eq_primeFactors_sdiff` proves

```lean
hfinite.toFinset =
  z.natAbs.primeFactors \ (quadraticBadPrimeModulus A).primeFactors
```

The factors already dividing `N_F` are therefore removed from the
additional product. Multiplying that product by `primeRadical N_F`
forms a disjoint union of prime-factor sets, which is the prime-factor
set of `N_F * z.natAbs`. This proves the equality of natural numbers

$$
N_G=\operatorname{primeRadical}(N_F\lvert z\rvert).
$$

It proves the exact modulus, rather than just agreement of its prime
divisors. Primes dividing both `N_F` and `z` occur once; no coprimality
assumption is used. The helper and the diagonal specialization
`diagonal_badPrimeModulus` both quantify over arbitrary `hfinite`, so
the result applies to the original modulus regardless of which valid
finiteness proof supplied its argument.

## Signs and the literal radical endpoint

`quadraticBadPrimeModulus_diagonal` proves `N_F = 2 * α.natAbs` for
the source product `α=∏ i, a i`. `diagonal_bad_modulus_product` proves

$$
N_F\lvert M\rvert=\lvert2\alpha M\rvert.
$$

Thus the final natural-number expression is precisely
`primeRadical (2 * (∏ i, a i) * diagonalPairProduct a b).natAbs`.
This expresses the source's `rad(2 α M)`: an integer and its absolute
value have the same positive prime divisors. Both `α` and `M` may be
negative. Their nonvanishing follows from the actual final hypotheses,
so the library's radical convention at zero is not used for this endpoint.

As a concrete check on the allowed hypotheses, `a=(1,1,1,2)` and
`b=(0,1,2,3)` give `α=2` and the six differences
`1,2,3,1,1,-1`, hence `M=-6`. This is a source instance with a zero
second-form coefficient and a negative pair product. No hypothesis in
the final export excludes either feature.

## Inspected dependencies and review conclusion

The actual `#check` types and `#print axioms` results for all 24 public
exports across the five modules were inspected after compilation. Every
one, including `diagonal_bad_primes`, has exactly the standard
foundational dependencies

```text
Classical.choice
Quot.sound
propext
```

There is no literature-premise dependency. In particular the result does
not use Lang elimination, Bertini, Katz, or the Weil bound. The square-root
existence over an algebraically closed field, matrix and polynomial
identities, rank/minor equivalence, and finite prime-factor arithmetic
are proved library or internal results. No new premise was introduced.

All five modules, including the complete `DiagonalBadPrimes.lean` wrapper,
passed compilation in the pinned Lean/mathlib environment with
`autoImplicit=false` and `warningAsError=true`. The inspected final type
contains the actual source objects, the required prime range, and all
three source conclusions under the source coefficient assumptions. This
review finds no omitted clause, strengthened hypothesis, or mathematical
gap.

The review supports Certified classification of Lemma 4.5 once the full
repository verification gates pass. The live ledger, verification report,
and execution checkpoint record those gates, the input hashes, and exact
commit/run evidence. This local completion does not assert certification
of the whole manuscript.
