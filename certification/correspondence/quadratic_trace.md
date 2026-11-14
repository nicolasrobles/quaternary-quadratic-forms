# Source correspondence: integrality, divisibility, and size of the quadratic trace

## Scope and source

This review covers the integrality and divisibility of the trace in Lemma
5.9, the bound `|a_p(G)| ≤ 4p` under the actual finite-field transversality
hypothesis, and their combination under the literal `N_G` condition with an
explicit proof that the bad-prime set is finite. Lemma 5.9 remains
**Partial**: the missing deduction is finiteness of that set from the
characteristic-zero smoothness assumption, as supplied by Lemma 4.1(i).
The size estimate itself is proved.

The source is the frozen v35
[manuscript](../../manuscript/quadratic_character_sums_github.tex), with SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The equation numbers below agree with the compiled labels in
[source.json](../source.json).

| Source location | Mathematical content | Corresponding declarations |
| --- | --- | --- |
| `eq:forms`, (1.1), lines 157–161 | The integral matrix expression `F(x) = xᵀ A x` | `matrixQuadraticPolynomial`, `eval_matrixQuadraticPolynomial_quadraticValue` |
| Lines 195–198 | The character is the Jacobi symbol, hence the Legendre symbol at an odd prime | `complexQuadraticChar`, `complexQuadraticChar_intCast` |
| `eq:smooth`, (1.9), lines 281–289; `eq:NG`, (1.10), lines 291–300 | Smoothness and the excluded primes | `GoodReductionAt`, `badReductionPrimes`, `polynomialBadPrimeModulus`, `not_dvd_polynomialBadPrimeModulus_iff`; characteristic-zero smoothness still has to supply the finiteness proof |
| `eq:apdef`, (1.11), lines 307–314 | The projective trace `a_p(G)` and independence of representatives | `projectiveQuadraticTrace`, `quadraticTraceWeight_rep_mk`, `projectiveQuadraticTrace_complex` |
| `lem:divisible`, Lemma 5.9, lines 2686–2690 | Integrality, divisibility by `p`, and the size bound | `projectiveTrace_quadratic_integral_dvd_bound`, `integralProjectiveTrace_quadratic_integral_dvd_bound`, and `integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus`; the last retains explicit `hfinite` |
| First sentence of the proof of Lemma 5.9 | The degree-two specialization of Lemma 2.7 | `projectiveQuadraticTrace_abs_le`, using `katz_quadric_bound_prime_field` |
| Proof of Lemma 5.9, lines 2694–2706 | Euler criterion, the polynomial zero-locus indicator, and the vanishing polynomial sum | `quadraticZeroIndicator_eval`, `quadraticCharacterPolynomial_sum_zero`, `affineQuadraticCharacterSum_dvd` |
| Proof of Lemma 5.9, lines 2706–2708; (4.4) and (4.5) | Passage from the affine sum to the projective trace | `affineQuadraticTrace_eq`, `projectiveQuadraticTrace_dvd` |

The files reviewed are
[AffineDivisibility.lean](../../QuaternaryQuadraticForms/AffineDivisibility.lean),
[MatrixPolynomial.lean](../../QuaternaryQuadraticForms/MatrixPolynomial.lean),
[QuadraticCharacter.lean](../../QuaternaryQuadraticForms/QuadraticCharacter.lean),
[QuadraticTrace.lean](../../QuaternaryQuadraticForms/QuadraticTrace.lean),
[QuadraticTraceBound.lean](../../QuaternaryQuadraticForms/QuadraticTraceBound.lean),
and [GoodReduction.lean](../../QuaternaryQuadraticForms/GoodReduction.lean).
`QuadraticTrace.lean` uses the previously checked zero-frequency identity. Its
[earlier correspondence review](fourier_rays.md) remains applicable.

## The character and the integer sums

The character in these proofs is mathlib's
`quadraticChar (ZMod p) : MulChar (ZMod p) ℤ`. Its values are the actual
integers `0`, `1`, and `-1`, with zero at the zero field element. The associated
complex character is defined by composition with `Int.castRingHom ℂ`.
Thus `complexQuadraticChar_apply` is an equality of the character value with
the complex cast of that integer. On an integer input,
`complexQuadraticChar_intCast` identifies it with `legendreSym p a`.
This is the source's character `(a/p)`, with the same order of numerator and
denominator.

`complexQuadraticChar_sq` proves that the square is the principal character,
including its zero-extension. `complexQuadraticChar_ne_one` verifies
nonprincipality at an odd prime. The divisibility argument itself uses the
integer character and Euler criterion; the square identity supplies the
character hypothesis of the previously proved ray formula.

Both integer traces have codomain `ℤ`:

$$
C_{\mathbb Z}=
\sum_{\substack{x\in\mathbf F_p^4\\x^{\mathsf T}Ax=0}}
\chi_p(G(x)),\qquad
a_{\mathbb Z}=
\sum_{P\in\mathcal Q(\mathbf F_p)}\chi_p(G(P)).
$$

They are defined by `affineQuadraticTrace` and `projectiveQuadraticTrace`.
Integrality therefore comes from the summands and the finite sums, with an
explicit integer available as the witness. No divisibility statement is
formed about an arbitrary complex number.

The identities `affineQuadraticTrace_complex` and
`projectiveQuadraticTrace_complex` prove that these integer sums, cast to
`ℂ`, are precisely the existing zero-frequency Fourier sum and the existing
projective trace. The Fourier phase at zero is one, and casting commutes with
the finite sums. In particular, the public conclusion
`projectiveTrace_quadratic_integral_dvd` states

```text
∃ a : ℤ, projectiveTrace A (complexQuadraticChar p) G = (a : ℂ)
         ∧ (p : ℤ) ∣ a.
```

Its witness is the defined integer projective trace, rather than a separate
integer whose relation to the original sum is assumed.

## The actual matrix form and projective quotient

The polynomial used for the matrix form is

$$
F_A(X)=\sum_i\sum_j A_{ij}X_iX_j.
$$

`eval_matrixQuadraticPolynomial` proves that evaluating it at `x` gives
`dotProduct x (A.mulVec x)`. The prime-field specialization identifies this
with the already defined `quadraticValue A x`. Homogeneity of degree two is
proved from the individual terms; its total degree is consequently at most
two. The argument applies to the actual matrix coefficients and does not
add an assumption that an unrelated polynomial represents the quadratic
form.

Projective points and the quadric are the same objects as in the earlier
Fourier checkpoint: mathlib's quotient of nonzero four-coordinate vectors by
nonzero scalar multiplication, restricted by `xᵀ A x = 0`. Membership in
that zero locus was already proved independent of the representative.

The definition of `projectiveQuadraticTrace` uses the chosen representative
`P.rep`. Its independence, as required by (1.11), is proved under
`G.IsHomogeneous 2` by `quadraticTraceWeight_rep_mk`. This follows from the
previous polynomial character scaling theorem and the injectivity of the
integer cast into `ℂ`. Thus both the index set and the integer summand have
the required quotient interpretation. Homogeneity is needed here even
though the affine divisibility theorem accepts arbitrary polynomials of
degree at most two.

## Euler criterion and the degree threshold

For polynomials `F` and `G` over `ZMod p` of total degree at most two, the
affine proof uses the literal polynomial

$$
H=(1-F^{p-1})G^{\lfloor p/2\rfloor}.
$$

The theorem `quadraticZeroIndicator_eval` proves that the first factor
evaluates to one at a zero of `F` and to zero elsewhere. It includes the zero
field element and uses the actual prime-field power identity.

Mathlib's Euler criterion,
`quadraticChar_eq_pow_of_char_ne_two'`, identifies the image of the integer
quadratic character in `ZMod p` with the power having exponent `p / 2`.
For an odd prime this is the source's exponent `(p-1)/2`. The implementation
keeps the library's exponent and proves the required strict inequality
directly:

$$
\deg H\leq 2(p-1)+2\lfloor p/2\rfloor<4(p-1).
$$

The inequality is checked from `p ≥ 3`, obtained from primality and `p ≠ 2`.
There is no use of a degree bound that becomes an equality at the vanishing
threshold. At an odd prime the displayed upper bound is exactly the source's
`3(p-1)`.

The official mathlib theorem `MvPolynomial.sum_eval_eq_zero`, in
`Mathlib.FieldTheory.ChevalleyWarning`, then gives

$$
\sum_{x\in\mathbf F_p^4}H(x)=0\quad\text{in }\mathbf F_p.
$$

Its degree threshold is `(card K - 1) * card σ`. Here `K = ZMod p` and
`σ = Fin 4`, so the threshold is precisely `4(p-1)`. This is the finite-field
monomial argument in the manuscript, already proved in the pinned library.

`affineQuadraticCharacterSum_dvd` identifies this field sum with the
reduction of the filtered integer character sum. It then applies
`ZMod.intCast_zmod_eq_zero_iff_dvd`. The matrix-polynomial adapter specializes
the result to `affineQuadraticTrace_dvd`, with the manuscript's actual
quadratic-form zero set.

## Passage to the projective trace and integral coefficients

For homogeneous quadratic `G`, the checked zero-frequency theorem gives,
after the two complex-cast identities and integer-cast injectivity,

$$
C_{\mathbb Z}=(p-1)a_{\mathbb Z}.
$$

This is `affineQuadraticTrace_eq`. Reducing it to `ZMod p`, the already
proved divisibility of `C_ℤ` gives `0 = -a_ℤ`. Hence the projective integer
trace is zero modulo `p`, and `projectiveQuadraticTrace_dvd` concludes
integer divisibility. The use of `p-1` is exact; no normalization by `p`,
by the number of projective points, or by a character factor enters.

The integral wrappers accept
`A : Matrix (Fin 4) (Fin 4) ℤ` and `G : MvPolynomial (Fin 4) ℤ`.
They reduce the coefficients with `Int.castRingHom (ZMod p)` and use the
previously proved `homogeneous_reduce_mod`. Consequently the caller supplies
homogeneity of the original integral form, without an extra unproved
homogeneity premise for its reduction.

## The finite-field size estimate

`projectiveQuadraticTrace_abs_le` specializes the proved prime-field form of
Lemma 2.7 to `n = 2` and `ψ = complexQuadraticChar p`.
`complexQuadraticChar_ne_one` verifies nonprincipality for the odd prime,
and `complexQuadraticChar_sq` verifies the required square identity. The
remaining inputs are the actual symmetric invertible matrix, homogeneous
quadratic `G`, and `ProjectiveIntersectionTransverseRank` over the algebraic
closure. The constant specializes exactly to

$$
2\cdot2^2-4\cdot2+4=4.
$$

The equality `projectiveQuadraticTrace_complex` identifies the complex sum
bounded by Katz with the cast of the defined integer trace. The library
identity `Complex.norm_intCast` and the checked cast conversion then give

$$
|\operatorname{projectiveQuadraticTrace}(A,G)|\le4p
\qquad\text{in }\mathbf Z.
$$

`projectiveTrace_quadratic_integral_dvd_bound` combines this estimate with
the existing integrality and divisibility proof. Its witness is the same
defined integer trace, and its conclusion is

```text
∃ a : ℤ, projectiveTrace A (complexQuadraticChar p) G = (a : ℂ)
         ∧ (p : ℤ) ∣ a ∧ |a| ≤ 4 * (p : ℤ).
```

The integral-coefficient exports
`integralProjectiveQuadraticTrace_abs_le` and
`integralProjectiveTrace_quadratic_integral_dvd_bound` accept
`p ∤ quadraticBadPrimeModulus A` and the literal predicate
`GoodReductionAt p A G`. Coefficient reduction, oddness, matrix symmetry,
and the nonzero reduced determinant are supplied by the existing proved
adapters. The review of the full Katz specialization and its explicit
composite literature boundary is in [katz_quadric.md](katz_quadric.md);
the size estimate is not introduced as a new premise.

## The literal good-reduction modulus

`badReductionPrimes A G` is the actual set of primes outside `N_F` at which
the reductions fail the geometric rank-two condition.
`polynomialBadPrimeModulus A G hfinite` is the product in (1.10):

$$
\operatorname{rad}(N_F)
\prod_{\substack{p\nmid N_F\\G\text{ has bad reduction at }p}}p.
$$

Its definition takes
`hfinite : (badReductionPrimes A G).Finite`. This is explicit proved data
required by the wrapper, not an axiom asserting that every polynomial has
finitely many bad primes. For `det A ≠ 0`,
`not_dvd_polynomialBadPrimeModulus_iff` proves that excluding this exact
modulus is equivalent to excluding `N_F` and having `GoodReductionAt p A G`.
The proof uses the prime divisors of the radical and of the actual finite
bad-prime product; it does not substitute an arbitrary larger modulus.

`integralProjectiveQuadraticTrace_dvd_bound_of_modulus` consequently gives
divisibility and the size bound for the defined integer trace.
`integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus` gives all
three clauses for the existing complex trace, using that integer as its
witness. Both wrappers retain `hfinite` as an explicit argument.

## Hypotheses and remaining scope

The final divisibility theorem assumes an odd prime and a homogeneous
quadratic polynomial. The manuscript's prime condition implies oddness:
`N_F = 2|det A|`, and `N_G` contains `rad(N_F)`, so every prime not dividing
`N_G` is different from two. The other manuscript hypotheses impose further
restrictions and are unnecessary for these two clauses.

| Manuscript hypothesis | Role in the completed clauses |
| --- | --- |
| A nonsingular symmetric integral matrix `A` | Symmetry and nonsingularity are used for the size bound; arbitrary matrix coefficients suffice for the polynomial identity and divisibility |
| A quadratic integral form `G` | Homogeneity of degree two is retained and preserved under reduction |
| Smoothness in (1.9) and good reduction at `p` | Good reduction is the actual geometric hypothesis of the proved size bound; characteristic-zero smoothness still has to imply finiteness of the bad-prime set |
| `p` prime with `p ∤ N_G` | The literal-modulus wrappers deduce oddness and good reduction, with the defining finiteness proof explicit; divisibility alone applies to every odd prime |
| The prime-field quadratic character | The actual integer-valued quadratic character is used, with an explicit Legendre-symbol identification |

Allowing singular matrices or a polynomial whose reduction becomes zero
does not invalidate the divisibility result. The affine degree proof still
applies; when needed for the ray identity, homogeneous quadratic weights
still vanish at the origin and are invariant under nonzero scaling. This
larger range of validity does not extend the claimed range of the separate
bound `|a_p(G)| ≤ 4p`.

The precise remaining obligation for Lemma 5.9 is to prove
`(badReductionPrimes A G).Finite` from the characteristic-zero rank condition
in (1.9), with the manuscript's integral homogeneous equations. This is
the finiteness part of Lemma 4.1(i). The elimination argument must provide
the missing proof; it cannot be replaced by the explicit `hfinite` argument
already accepted by the wrappers. The quantitative height bound in Lemma
4.1(i) is a further obligation of that lemma, but is not required to close
Lemma 5.9 once finiteness is proved.

Thus all three trace conclusions are proved under explicit finite-field
good reduction, and they are combined under the actual `N_G` condition
conditional on its defining finite bad-prime set. This is not yet the full
statement of Lemma 5.9 from characteristic-zero smoothness. The appropriate
classification remains **Partial** for that precise reason.

This review records mathematical correspondence and scope. Numbered-result
counts, build results, axiom reports, file hashes, checked commits, and CI
evidence belong to the status and execution records.
