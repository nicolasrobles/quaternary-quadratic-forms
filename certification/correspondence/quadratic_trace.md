# Source correspondence: integrality and divisibility of the quadratic trace

## Scope and source

This review covers the assertions that the trace in Lemma 5.9 is an integer
and is divisible by the prime. The remaining assertion, `|a_p(G)| ≤ 4p`, is
outside this checkpoint. The appropriate status for Lemma 5.9 is **Partial**.

The source is the frozen v35
[manuscript](../../manuscript/quadratic_character_sums_github.tex), with SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The equation numbers below agree with the compiled labels in
[source.json](../source.json).

| Source location | Mathematical content | Corresponding declarations |
| --- | --- | --- |
| `eq:forms`, (1.1), lines 157–161 | The integral matrix expression `F(x) = xᵀ A x` | `matrixQuadraticPolynomial`, `eval_matrixQuadraticPolynomial_quadraticValue` |
| Lines 195–198 | The character is the Jacobi symbol, hence the Legendre symbol at an odd prime | `complexQuadraticChar`, `complexQuadraticChar_intCast` |
| `eq:smooth`, (1.9), lines 281–289; `eq:NG`, (1.10), lines 291–300 | Smoothness and the excluded primes | These stronger hypotheses belong to the full lemma; oddness is sufficient for its divisibility clause |
| `eq:apdef`, (1.11), lines 307–314 | The projective trace `a_p(G)` and independence of representatives | `projectiveQuadraticTrace`, `quadraticTraceWeight_rep_mk`, `projectiveQuadraticTrace_complex` |
| `lem:divisible`, Lemma 5.9, lines 2686–2690 | Integrality, divisibility by `p`, and the separate size bound | `projectiveTrace_quadratic_integral_dvd`, `integralProjectiveTrace_quadratic_dvd`; size bound pending |
| Proof of Lemma 5.9, lines 2694–2706 | Euler criterion, the polynomial zero-locus indicator, and the vanishing polynomial sum | `quadraticZeroIndicator_eval`, `quadraticCharacterPolynomial_sum_zero`, `affineQuadraticCharacterSum_dvd` |
| Proof of Lemma 5.9, lines 2706–2708; (4.4) and (4.5) | Passage from the affine sum to the projective trace | `affineQuadraticTrace_eq`, `projectiveQuadraticTrace_dvd` |

The files reviewed are
[AffineDivisibility.lean](../../QuaternaryQuadraticForms/AffineDivisibility.lean),
[MatrixPolynomial.lean](../../QuaternaryQuadraticForms/MatrixPolynomial.lean),
[QuadraticCharacter.lean](../../QuaternaryQuadraticForms/QuadraticCharacter.lean),
and [QuadraticTrace.lean](../../QuaternaryQuadraticForms/QuadraticTrace.lean).
The last file uses the previously checked zero-frequency identity. Its
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

Both new traces have codomain `ℤ`:

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

## Hypotheses and remaining scope

The final divisibility theorem assumes an odd prime and a homogeneous
quadratic polynomial. The manuscript's prime condition implies oddness:
`N_F = 2|det A|`, and `N_G` contains `rad(N_F)`, so every prime not dividing
`N_G` is different from two. The other manuscript hypotheses impose further
restrictions and are unnecessary for these two clauses.

| Manuscript hypothesis | Role in the completed clauses |
| --- | --- |
| A nonsingular symmetric integral matrix `A` | Arbitrary matrix coefficients suffice for the polynomial identity and divisibility |
| A quadratic integral form `G` | Homogeneity of degree two is retained and preserved under reduction |
| Smoothness in (1.9) and good reduction at `p` | Not used in the integrality or divisibility proof; retained for the pending size estimate |
| `p` prime with `p ∤ N_G` | The completed theorem applies to every odd prime |
| The prime-field quadratic character | The actual integer-valued quadratic character is used, with an explicit Legendre-symbol identification |

Allowing singular matrices or a polynomial whose reduction becomes zero
does not invalidate the divisibility result. The affine degree proof still
applies; when needed for the ray identity, homogeneous quadratic weights
still vanish at the origin and are invariant under nonzero scaling. This
larger range of validity does not extend the claimed range of the separate
bound `|a_p(G)| ≤ 4p`.

No mathematical or source-correspondence defect was found in the reviewed
integrality and divisibility statements. Lemma 5.9 should therefore be
**Partial**, with those two clauses checked and its size estimate pending.
That estimate is the `n=2` specialization of Lemma 2.7, together with the
required geometric hypotheses and their verification. It has not been
inserted as an assumption in these proofs.

The resulting numbered counts are **Complete 0 / Partial 2 / Active 0 /
Pending 40**. Lemma 4.4 retains its previous Partial scope; all 33 auxiliary
or supplementary groups remain Pending. The present proof reuses the
completed zero-frequency identity and does not close the remaining Fourier
estimate or any main theorem.

The new root assembly module compiled with `warningAsError=true` and
`autoImplicit=false` in the pinned environment. This review records its
mathematical correspondence and scope. The repository verifier and execution
records provide the actual theorem types, axiom dependencies, file hashes,
and exact checked commit and CI run; no CI success is asserted by this
correspondence review alone.
