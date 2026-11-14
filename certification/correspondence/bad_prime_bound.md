# Source correspondence: Lemma 3.3

## Scope and frozen source

This review concerns the full assertion of `lem:badprime`, Lemma 3.3:

$$
|S_c(u)|\le 4|\alpha|^{1/2}c^3
\qquad(c\ge1,\ u\in\mathbb Z^4).
$$

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | The nonsingular symmetric integral matrix, `F(x)=xᵀAx`, `α=det A`, and the global nonsquare convention |
| Notation, lines 561–572 | The positive additive character `e_c(t)=exp(2πit/c)` and the meaning of a sum over reduced residues |
| `eq:Sdef`, lines 1029–1035 | The actual complete sum `S_c(u)` over unit parameters and four-coordinate residue vectors |
| `lem:badprime`, `eq:badbound`, lines 1156–1161 | The uniform bound for every positive modulus and every integral frequency |
| Lines 1163–1170 | Translation in the product with the conjugate and additive orthogonality selecting the kernel of `2A` |
| Lines 1171–1177 | The determinant bound for that kernel, the exact factor four, and summation over reduced residues |

The preceding sentence about primes dividing `N_F` explains the use of
the estimate. It does not restrict the displayed statement to prime
powers or to moduli supported on bad primes. The formal endpoint covers
every positive modulus, as the statement requires.

## Modules and reviewed exports

| Module | Public exports | Reviewed role |
| --- | ---: | --- |
| [GaussNorm.lean](../../QuaternaryQuadraticForms/GaussNorm.lean) | 3 | Composite-modulus orthogonality, the exact product with the conjugate, and the squared-norm kernel bound |
| [MatrixResidueKernel.lean](../../QuaternaryQuadraticForms/MatrixResidueKernel.lean) | 1 | The actual finite residue kernel and its membership characterization |
| [IntegerMatrixKernelBound.lean](../../QuaternaryQuadraticForms/IntegerMatrixKernelBound.lean) | 1 | Bounding that actual kernel by the absolute integer determinant |
| [GaussBoundConstants.lean](../../QuaternaryQuadraticForms/GaussBoundConstants.lean) | 4 | The determinant factor sixteen, the square-root factor four, and the unit-cardinality bound |
| [DoubledMatrixKernel.lean](../../QuaternaryQuadraticForms/DoubledMatrixKernel.lean) | 2 | Identifying the kernel selected by polarization with the reduction of the doubled integer matrix |
| [CompleteSumNorm.lean](../../QuaternaryQuadraticForms/CompleteSumNorm.lean) | 1 | Applying a common inner Gauss bound to the actual outer unit sum |
| [BadPrimeGaussBound.lean](../../QuaternaryQuadraticForms/BadPrimeGaussBound.lean) | 3 | The squared and unsquared inner estimates from the source matrix hypotheses |
| [BadPrimeBound.lean](../../QuaternaryQuadraticForms/BadPrimeBound.lean) | 2 | The complete-sum estimate and the exact source statement with real absolute value |

These are seventeen public theorem exports in eight modules. The
definition `matrixResidueKernel` is also new; it is an arithmetic
object, not an additional numbered result. The inner bounds and the
index calculation support the single conclusion of Lemma 3.3.

## The actual Gauss and complete sums

The existing
[QuadraticGaussSums.lean](../../QuaternaryQuadraticForms/QuadraticGaussSums.lean)
defines

```lean
quadraticGaussSum n A a u :=
  ∑ x : Fin 4 → ZMod n,
    ZMod.stdAddChar (a * dotProduct x (A.mulVec x) + dotProduct u x)
```

The standard character has the source's positive phase. The existing
[IntegralGaussSums.lean](../../QuaternaryQuadraticForms/IntegralGaussSums.lean)
connects coefficient reduction to canonical integer representatives
and proves

```lean
unweightedCompleteSum n A u =
  ∑ a : (ZMod n)ˣ,
    quadraticGaussSum n (A.map (Int.castRingHom (ZMod n)))
      (a : ZMod n) (fun i => (u i : ZMod n))
```

Thus the terminal estimate concerns exactly the `S_c(u)` already
identified with `eq:Sdef`. No abstract sum, alternative phase, or
unspecified cardinality is substituted for the source objects. The
integral frequency is reduced only to evaluate its actual residue
character; the final theorem retains the original `u : Fin 4 → ℤ`.

## Translation and orthogonality at arbitrary moduli

For the actual summand

$$
f(x)=e_n\bigl(a\,x^{\mathsf T}Ax+u\cdot x\bigr),
$$

symmetry gives the exact identity

$$
f(x+z)\overline{f(x)}
=f(z)e_n\bigl(2a\,x^{\mathsf T}Az\bigr).
$$

`GaussNorm.lean` proves this identity by expanding the quadratic value,
using `A.transpose=A` for the two cross terms, and using that conjugation
of the standard character negates its argument. The change from the
second summation variable to `x+z` is the actual equivalence
`Equiv.addLeft x` on all residue vectors.

`stdAddChar_residue_vector_orthogonality` separates the four coordinates
and applies the proved primitive-standard-character orthogonality
theorem over `ZMod n`. Its result is `n^4` when the coefficient vector
is zero and zero otherwise. It requires `[NeZero n]`, not primality,
a field instance, or invertibility of two.

For a unit parameter `a`, the coefficient vector vanishes exactly when
`2 • A.mulVec z=0`. Cancellation uses the unit `a`; it never cancels
two or the matrix. This distinction preserves the correct kernel at
even moduli and at primes of bad reduction.

The public identity `quadraticGaussSum_mul_conj_eq_kernel_sum` is
therefore the literal equality

$$
V\overline V
=n^4\sum_{\substack{z\bmod n\\2Az=0}}
e_n\bigl(a\,z^{\mathsf T}Az+u\cdot z\bigr).
$$

Taking complex norms and using the triangle inequality and the unit
norm of every standard-character value gives
`quadraticGaussSum_norm_sq_le_kernel_card`:

$$
\|V\|^2\le n^4\#\{z\bmod n:2Az=0\}.
$$

This proves the real inequality implicit in the source's displayed
calculation. The proof does not put an order on the intervening complex
sum, assume positivity of its individual terms, or assume a value for
the kernel cardinality.

## The actual integer-matrix kernel bound

`matrixResidueKernel n B` is defined as

```lean
Finset.univ.filter fun z : Fin 4 → ZMod n =>
  (B.map (Int.castRingHom (ZMod n))).mulVec z = 0
```

`mem_matrixResidueKernel` proves precisely this membership condition.
For every nonsingular integral matrix `B`, the public theorem
`matrixResidueKernel_card_le_det` proves

$$
\#\ker(B\bmod n)\le |\det B|.
$$

The proof organizes the source's Smith-normal-form argument through
the proved determinant-index theorem in the pinned mathlib:

1. Put `f := Matrix.toLin' B` on `ℤ⁴`. The equality
   `LinearMap.det_toLin'` identifies its determinant with `B.det`.
   `LinearMap.det_eq_zero_iff_ker_ne_bot` proves injectivity from
   `B.det≠0`, so `LinearEquiv.ofInjective f` gives the actual equivalence
   from `ℤ⁴` onto `LinearMap.range f`.
2. Apply `Submodule.natAbs_det_equiv` to this range equivalence. Its
   composition with the range subtype is the original matrix map, so
   the resulting index is exactly `B.det.natAbs`. The mathlib theorem
   proves the determinant-index formula using Smith normal form; it
   is not a registered literature premise.
3. Define coordinate reduction `ρ : ℤ⁴ →+ (ZMod n)⁴`. Surjectivity is
   proved with canonical residue lifts. Reduction is proved to commute
   with the actual matrix maps, and hence maps the integer range onto
   the actual residue range.
4. Apply `AddSubgroup.index_map_dvd`. The residue-range index divides
   the integer-range index. For the finite residue endomorphism,
   `AddSubgroup.index_range` identifies that index with the cardinality
   of its actual additive kernel.
5. `Fintype.card_subtype` identifies this kernel cardinality with the
   cardinality of the defining filtered finite set. Positivity of
   `B.det.natAbs` then turns the proved divisibility into the bound.

In particular, the proof internally obtains

$$
\#\ker(B\bmod n)\mid |\det B|.
$$

The newly exported conclusion is the determinant bound. There is no
newly exported exact product-of-gcd formula, and this review does not
claim one. The determinant-index organization proves the same bound
needed in the source by using the library's already proved Smith
normal form. All maps, ranges, and finite sets in the argument belong
to the given matrix and modulus. No kernel estimate, range-index
identity, or nonsingularity modulo `n` is assumed.

## The doubled matrix and the exact constants

`reduceQuadraticMatrix_two_smul` proves that reducing the integer
matrix `2 • A` gives `2 • reduceQuadraticMatrix n A`.
`matrixResidueKernel_two_smul` consequently identifies its actual
finite kernel with the set selected by the Gauss-norm calculation.

For the four-coordinate matrix, `quaternary_det_two_smul` and
`quaternary_det_two_smul_natAbs` prove

$$
\det(2A)=16\det A,
\qquad
|\det(2A)|=16|\det A|.
$$

Since `A.det≠0`, the doubled integer matrix is also nonsingular. The
kernel theorem therefore applies even when its residue reduction is
singular. Combining the proved bounds gives
`quadraticGaussSum_integral_norm_sq_le`:

$$
\|V\|^2\le n^4\bigl(16|\det A|\bigr).
$$

`gauss_norm_le_of_sq_le` checks the nonnegative real square root and
the exact square of the proposed upper bound. Applying it with
`D=(A.det.natAbs : ℝ)` yields
`quadraticGaussSum_integral_norm_le`:

$$
\|V\|\le4\sqrt{|\det A|}\,n^2.
$$

This theorem holds for every residue frequency and every actual unit
parameter. `integralQuadraticGaussSum_norm_le` also states it for the
literal integer data whenever the scalar's reduction is a unit, as
in the source's inner sum. No asserted Gauss evaluation or assumed
inner norm estimate is used to obtain these bounds.

## Summation over units and the terminal source statement

`unweightedCompleteSum_norm_le_of_gauss_bound` is a composition helper:
it accepts a common bound `K` for the actual inner sums and proves
`‖S_n(u)‖≤n*K`. It applies the triangle inequality to the existing
complete-sum identity. Its required nonnegativity of `K` follows from
the bound at the unit `1`. The theorem `zmod_card_units_le` proves

$$
\#(\mathbb Z/n\mathbb Z)^\times\le n
$$

using the injective map from units to their residue values. This works
also for modulus one.

The final theorem supplies the helper's entire premise from
`quadraticGaussSum_integral_norm_le`. Thus `K` and the family of inner
estimates are discharged deductions, not assumptions in the source
endpoint. Multiplying the bound `4√|det A| n²` by `n` gives the exact
power `n³`.

The complete source theorem is
`QuaternaryQuadraticForms.bad_prime_bound`:

```lean
theorem bad_prime_bound (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (u : Fin 4 → ℤ) :
    ‖unweightedCompleteSum c A u‖ ≤
      4 * Real.sqrt |(A.det : ℝ)| * (c : ℝ) ^ 3
```

`unweightedCompleteSum_norm_le` first gives the same statement with
`(A.det.natAbs : ℝ)`. The proved cast identities
`Nat.cast_natAbs` and `Int.cast_abs` give the displayed source
convention, so negative determinants are handled by real absolute
value before taking the nonnegative square root.

| Source assumption or convention | Treatment in the terminal theorem |
| --- | --- |
| Every integer modulus `c≥1` | `c : ℕ` with `[NeZero c]`; nonzero natural numbers are exactly the positive natural values of the source's positive integers. No positive modulus is omitted. |
| Integral symmetric `4×4` matrix | Exactly the matrix type and equality `A.transpose=A`; symmetry is used in polarization. |
| Nonsingularity over the integers | Exactly `A.det≠0`, essential for the positive determinant bound on the kernel. |
| Arbitrary `u∈ℤ⁴` | The unchanged integral frequency, including zero, with no primitivity or nonvanishing condition. |
| `α=det A` | The determinant of that same integer matrix throughout the kernel and norm bounds. |
| Absolute value of `S_c(u)` | The usual complex norm of the actual `unweightedCompleteSum`. |
| Square root of the absolute determinant | `Real.sqrt (abs (A.det : ℝ))`; the determinant is not assumed positive. |
| Reduced residues in the outer sum | The actual unit group `(ZMod c)ˣ`, connected to the existing source definition. |
| Global nonsquareness of `α` | Unused by this estimate. Omitting it strengthens the result and retains every source instance. |
| Prime divisors of the modulus | No restriction: the theorem includes even, composite, good-prime, and bad-prime moduli. |

There is no good-prime, oddness, coprimality-with-`N_F`, or modular
matrix-invertibility hypothesis. At `c=1`, the residue vector space
and unit group each have one element, and the sums contain their
single character value one. All proofs above include this case; none
uses nontriviality of the residue ring. The standing integer
nonsingularity remains essential: a singular integer matrix would
give a zero proposed determinant bound although its kernel contains
the zero vector.

## Inspected dependencies and review conclusion

The actual `#check` and `#print axioms` inspection completed successfully
for all seventeen new public exports. The printed terminal type is
exactly the statement displayed above. Every new export has exactly

```text
Classical.choice
Quot.sound
propext
```

No registered literature premise occurs in these dependencies. The
standard-character orthogonality, finite-sum reindexing, determinant
index, subgroup-index identities, and real square-root facts are
proved in the pinned mathlib or the repository. The conditional
complete-sum helper is fully discharged in `bad_prime_bound`; no
internal manuscript estimate is promoted to an external assumption.

All eight modules passed strict compilation with the pinned Lean
4.24.0 toolchain, and the targeted build completed successfully. The
independent review of their definitions, proofs, and printed theorem
types finds the full source assertion present, all source instances
covered, and no mathematical gap. In particular, the review checks the
actual doubled-matrix kernel at even moduli, its finite-set cardinality
bridge, the integral determinant index, the constants sixteen and four,
the actual unit sum, and the absence of a surviving conditional bound.

This completed correspondence review supports Certified classification
of Lemma 3.3 when the full repository verification gates pass. At the
time this review was frozen, the module builds and seventeen-export
type/dependency inspection were complete; the full aggregate gate and
the subsequent exact-commit CI gate were still pending. The live
ledger, verification report, and execution checkpoint record the
eventual checked hashes and publication evidence.

The milestone adds seventeen exports, eight modules, and this review,
giving 553 registered exports, 120 proof modules, and 146 inspected
inputs at integration. The numbered-result scope is 13 Certified,
0 Partial, 0 Active, and 29 Pending; the 33 auxiliary Pending groups
remain distinct. The four registered literature premises, twenty
mapped reference groups, and nine pinned dependency revisions are
unchanged. The shared-prime mixed sum of Lemma 3.4 and the other
pending manuscript obligations remain separate.
