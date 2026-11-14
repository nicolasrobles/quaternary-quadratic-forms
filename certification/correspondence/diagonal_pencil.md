# Source correspondence: Lemma 4.6

## Scope and frozen source

This review covers all three assertions of `lem:pencil`, Lemma 4.6: the
exact formula for every integral frequency, the projective trace identity,
and the bound `2 p^(3/2) + 4 p` under the literal generic-frequency
nondivisibility condition. It also checks the pencil polynomials, singular
parameters, Gauss identities, and repeated-root cubic argument used in the
deduction.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Content |
| --- | --- |
| `eq:forms`, lines 157–164, and `eq:diagonal`, lines 205–208 | The two integral diagonal forms, `α = ∏ a_i`, and the six pair differences |
| `eq:apdef`, lines 310–316 | The actual projective quadratic-character trace `a_p(G)` |
| `eq:kappadef`, lines 383–386 | The signs and orientations in `κ_i` and the six-factor product `M` |
| `eq:diagtrace`, lines 391–393 | The trace identity `a_p(G) = p ∑ χ_p(κ_i)` |
| `eq:dualform`, lines 814–817 | The dual form `F*(u) = uᵀ adj(A) u` |
| `eq:ramanujan`, lines 1043–1046 | The sum over invertible residue classes defining `R_n` |
| `eq:Cpsi`, lines 1598–1603 | The cone Fourier sum with the positive phase `e_p(u · x)` |
| Lines 1884–1895; `eq:pencilforms` | The good-prime restriction, four singular parameters, `Φ_u`, and `ν_i` |
| `lem:pencil`, lines 1897–1908; `eq:exactpencil`, `eq:diagbound` | The three conclusions reviewed here |
| Lines 1911–1955 | Additive orthogonality, quadratic Gauss inversion, and the regular and singular contributions |
| Lines 1957–1976 | The trace specialization and the separable/repeated-root cubic bound |

The following paragraph, lines 1979–1983, uses this lemma in the later
analytic argument. It is not an additional clause of Lemma 4.6, and this
review does not certify the remaining asymptotic conclusion of Theorem 1.3.

## Modules and review boundary

| Module | Reviewed role |
| --- | --- |
| [DiagonalPencil.lean](../../QuaternaryQuadraticForms/DiagonalPencil.lean) | Literal coefficients, `κ_i`, `Φ_u`, `ν_i`, products, reciprocal phases, and coefficient maps |
| [DiagonalPencilAlgebra.lean](../../QuaternaryQuadraticForms/DiagonalPencilAlgebra.lean) | Root identities, distinctness, prime range, and exact regular/singular rational identities |
| [DiagonalPencilCubic.lean](../../QuaternaryQuadraticForms/DiagonalPencilCubic.lean) | Polynomial degree and identification with the actual adjugate quadratic form |
| [PrimeQuadraticGauss.lean](../../QuaternaryQuadraticForms/PrimeQuadraticGauss.lean) | The actual Gauss sum, inversion, completion of the square, and the zero quadratic coefficient |
| [PrimeRamanujan.lean](../../QuaternaryQuadraticForms/PrimeRamanujan.lean) | The literal prime Ramanujan sum, both of its values, and nonzero scaling |
| [FourierOrthogonality.lean](../../QuaternaryQuadraticForms/FourierOrthogonality.lean) | Expansion of the actual cone condition and factorization of the positive Fourier phase |
| [FourierGaussExpansion.lean](../../QuaternaryQuadraticForms/FourierGaussExpansion.lean) | Removal of the zero Gauss parameter and the exact substitution `v = s t` |
| [DiagonalPencilEvaluation.lean](../../QuaternaryQuadraticForms/DiagonalPencilEvaluation.lean) | Exact regular and singular contributions before cancellation of `p τ_p` |
| [DiagonalPencilFormula.lean](../../QuaternaryQuadraticForms/DiagonalPencilFormula.lean) | Splitting at the actual four roots and the complete prime-field pencil formula |
| [CubicCharacterSum.lean](../../QuaternaryQuadraticForms/CubicCharacterSum.lean) | Perfect-field descent for repeated cubic roots, their exact character sum, and the cubic bound |
| [DiagonalPencilReduction.lean](../../QuaternaryQuadraticForms/DiagonalPencilReduction.lean) | Reduction of the two literal integral nondivisibility conditions and of the adjugate value |
| [DiagonalPencilConsequences.lean](../../QuaternaryQuadraticForms/DiagonalPencilConsequences.lean) | The actual integer projective trace and the generic-frequency bound |
| [DiagonalPencilTheorem.lean](../../QuaternaryQuadraticForms/DiagonalPencilTheorem.lean) | The three integral source clauses and the complete `diagonal_pencil` export |

All thirteen modules and the final integral wrapper have passed strict
compilation in the pinned Lean/mathlib environment and have been reviewed
against the frozen source. The actual types and axiom lists of all 67 new
public exports have also been inspected. The source-correspondence review
is complete; Certified classification remains subject to the full
repository verification gate, as described below.

## Literal source objects and maps

The index type `Fin 4` represents the four source coordinates, with the
order-preserving relabeling `0,1,2,3` to `1,2,3,4`. Both forms remain the
existing `matrixQuadraticPolynomial (Matrix.diagonal a)` and
`matrixQuadraticPolynomial (Matrix.diagonal b)`. The previously checked
`diagonalQuadraticPolynomial_eq_sum` identifies these formal polynomials
with the actual sums of coefficient-weighted squares.

The new definitions are exactly

$$
c_i(t)=b_i+t a_i,\qquad
\kappa_i=-a_i\prod_{j\ne i}(a_i b_j-a_j b_i),
$$

$$
\Phi_u=\sum_i C(u_i^2)\prod_{j\ne i}(C(b_j)+X C(a_j)),
\qquad
\nu_i(u)=\sum_{j\ne i}u_j^2
                 \prod_{l\ne i,j}(a_i b_l-a_l b_i).
$$

The products use `univ.erase i` and `(univ.erase i).erase j`, so they have
three and two factors respectively. The sign in `κ_i` is the source sign;
there is no absolute value or reorientation of its factors.
`diagonalPairProduct`, already reviewed for Lemma 4.5, is the product of
the six factors with `i < j`, rather than the product over twelve ordered
pairs.

`diagonalPencilPhi_map` is an identity of formal polynomials under every
coefficient homomorphism. The corresponding maps for `c_i`, `κ_i`, and
`ν_i` are also proved. Consequently reduction of the integer source
expressions gives precisely the prime-field expressions used in the sum.
It is not an identification based only on agreement of finite-field
evaluation functions.

`eval_diagonalPencilPhi` gives the displayed source evaluation sum.
`eval_diagonalPencilPhi_eq_dual` proves for every parameter that this value
equals the quadratic form of the adjugate of `diag(c_i(t))`, including
singular parameters. The adjugate is defined even when its matrix is
singular.

`diagonalPencilPhi_natDegree_le` proves the bound three over every
commutative coefficient ring. The top coefficient is

$$
[X^3]\Phi_u=\sum_i u_i^2\prod_{j\ne i}a_j
           =u^{\mathsf T}\operatorname{adj}(\operatorname{diag}(a))u.
$$

Both the matrix-value identity and equality with evaluation of the
literal multivariate matrix polynomial are exported. The nonzero dual
value then proves `natDegree = 3`; cubic degree is derived, not separately
assumed for the source pencil.

The Fourier sum is the existing `fourierSum`, whose summation set is the
actual four-dimensional prime-field cone `F(x)=0`, whose weight is
`complexQuadraticChar p (G(x))`, and whose phase is
`ZMod.stdAddChar (dotProduct u x)`. The latter is the positive phase in
`eq:Cpsi`; no conjugation or replacement of `u` by `-u` occurs.
`complexQuadraticChar` is the integer-valued quadratic character followed
by the integer-to-complex homomorphism and is extended by zero at zero.
Its values on reduced integers are the source Legendre symbols.

## Exact good-prime hypotheses and singular parameters

`diagonalPencil_reduced_data` starts from the single literal restriction

```lean
¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b
```

under `[Fact p.Prime]`. Reduction modulo `p` turns it into nonvanishing of
the same product in `ZMod p`. The proof derives odd characteristic, every
`a_i ≠ 0`, and every pair difference with distinct indices nonzero.
Reversing the order of a pair changes only its sign, using the previously
proved six-factor criterion.

Over an arbitrary field, the actual singular parameter is
`diagonalPencilRoot a b i = -b i / a i`. The coefficient identity is

$$
c_j(t_i)=\frac{a_i b_j-a_j b_i}{a_i}.
$$

Thus `c_i(t)=0` if and only if `t=t_i`; at `t_i` every coefficient other
than the `i`th is nonzero. If two roots agreed, the coefficient belonging
to one index would be both zero and nonzero at the other root.
`diagonalPencilRoot_injective` proves their distinctness this way.

`diagonalPencilRoots` is the image of these four roots. The formula uses
its complement as the regular-parameter set. Its cardinality is at most
four without assumptions, and injectivity ensures that summing over the
root set counts all four indexed singular contributions exactly once.
Injectivity into `ZMod p` gives `4 ≤ p`; primality excludes `p=4`, so
`five_le_of_diagonalPencil_roots` derives `5 ≤ p`. This is not an added
prime-range assumption in the integral source theorem.

No coefficient `b_i` is required to be nonzero. If `b_i=0`, then `t_i=0`,
which is retained as one of the four singular parameters. Neither signs
of the integral coefficients nor signs of `α` and `M` are restricted.
The standing nonsquare-determinant assumption is unused in this finite
character-sum identity and bound. The prime restriction already supplies
the nonvanishing needed after reduction.

## Gauss identities and the Fourier expansion

`primeQuadraticGauss` is the actual finite Gauss sum

$$
\tau_p=\sum_{s\in\mathbf F_p}\chi_p(s)e_p(s).
$$

Mathlib's proved Gauss-sum results give its nonvanishing at odd primes
and the identity `τ_p² = χ_p(-1) p`. Squaring yields `τ_p⁴ = p²`.
No choice of a complex square root of `p` or a convention for its sign is
introduced.

Gauss inversion is proved at every argument, including zero. For a
nonzero argument the proof uses multiplication by a field unit and the
quadratic character's square-one identity. At zero, the sum of the
nonprincipal quadratic character is zero. The zero summand in the Gauss
parameter is then removed because `χ_p(0)=0`, giving an equivalent sum
over `(ZMod p)ˣ`. Inversion permutes those units and preserves their
quadratic-character values, which justifies the reciprocal phase used
later.

`primeQuadraticExponentialSum` is the literal sum
`∑ y, e_p(c y² + w y)`. If `c ≠ 0`, a proved square-root count gives the
unshifted Gauss evaluation, and translating by `w/(2c)` completes the
square:

$$
\sum_y e_p(cy^2+wy)
  =\chi_p(c)\tau_p e_p(-w^2/(4c)).
$$

If `c=0`, additive orthogonality gives `p` when `w=0` and zero otherwise.
Both cases are needed; the singular members are not excluded from the
one-dimensional calculation.

`fourierSum_additive_expansion` expands the literal constraint `F(x)=0`
using `∑_v e_p(v F(x))`. It proves the equality with `p C_p(u)`, so its
normalization is explicit. Gauss inversion then gives `p τ_p C_p(u)` as
a sum over the unit parameter `s`, the unrestricted parameter `v`, and
the actual vectors `x`. Only after `s` is a unit is `v=s t` introduced;
multiplication by `s` is a proved bijection of the prime field.

The diagonal identity expresses the entire phase as

$$
\sum_i\bigl(s(b_i+t a_i)x_i^2+u_i x_i\bigr).
$$

The additive character sends this sum to a product, and the finite sum
over four independent coordinates becomes the product of four genuine
one-dimensional sums. The result is exactly `eq:pencilsum`, expressed
after multiplication by the nonzero factor `p τ_p`. All values of `t`
remain present.

## Regular contribution

For a regular parameter, all four `c_i(t)` are nonzero and
`Δ(t)=∏_i c_i(t)` is nonzero. The internally proved rational identity is

$$
\frac{\Phi_u(t)}{\Delta(t)}=\sum_i\frac{u_i^2}{c_i(t)}.
$$

The four completed-square factors have their stated Gauss powers,
quadratic characters, and reciprocal additive phase. Quadratic-character
fourth powers at units equal one. Reciprocal Gauss inversion and
`τ_p⁴=p²` then give the raw contribution

$$
p^2\tau_p\chi_p(-\Phi_u(t)).
$$

The factor `1/4` in the phase is removed only through the explicitly
nonzero square `2^{-2}`. The minus sign is retained. This calculation
holds whether or not `Φ_u(t)` vanishes; character zero is included.

## Singular contributions, including zero Ramanujan arguments

At `t_i` the `i`th one-dimensional quadratic coefficient is zero. Its
factor is zero if `u_i ≠ 0` and is `p` if `u_i=0`. All three other
coefficients are nonzero, giving the literal quantities

$$
\Delta_i=\prod_{j\ne i}c_j(t_i),\qquad
W_i=\sum_{j\ne i}\frac{u_j^2}{c_j(t_i)}.
$$

The product calculation, including the outer quadratic-character weight,
uses `χ_p(s)^4=1` and `τ_p²=χ_p(-1)p`. Its raw value when `u_i=0` is

$$
p^2\tau_p\chi_p(-\Delta_i)R_p(W_i).
$$

`primeRamanujan` is defined as the actual sum of `e_p(s c)` over units,
matching the prime specialization of `eq:ramanujan`. The two values are
proved directly from additive orthogonality:

$$
R_p(c)=\begin{cases}p-1&c=0,\\-1&c\ne0.\end{cases}
$$

Inverting the unit parameter and multiplying its argument by a nonzero
scalar preserve this sum. In particular, the reciprocal phase
`-W_i/(4s)` gives exactly `R_p(W_i)`.

The two exact source-algebra identities are

$$
-\Delta_i=\frac{\kappa_i}{a_i^4},\qquad
W_i=\frac{\nu_i(u)}{a_i^2\Delta_i}.
$$

The proof also establishes `Δ_i ≠ 0` and `κ_i ≠ 0`. The denominator in
the second formula is therefore nonzero. The fourth power in the first
formula leaves the quadratic character unchanged; the nonzero scalar in
the second leaves the Ramanujan value unchanged. This gives the exact raw
singular contribution

$$
p^2\tau_p\,\mathbf 1_{u_i=0}\,
  \chi_p(\kappa_i)R_p(\nu_i(u)).
$$

There is no assumption that `ν_i(u)` is nonzero and no replacement of all
Ramanujan values by `-1`. The potentially large `p-1` value remains in
the formula, including at `u=0` and at other exceptional frequencies.

## Assembly and the projective trace

`diagonalPencil_sum_split` partitions the complete parameter sum into the
complement of the actual root set and the four indexed singular values.
Root injectivity justifies the image-sum identity without multiplicity.
`diagonal_fourier_pencil_formula` applies the regular and singular raw
evaluations and cancels the proved nonzero complex factor `p τ_p`.
The result has exactly the two terms in `eq:exactpencil`, with the second
sum filtered by `u_i=0` in the prime field.

At zero frequency the formal polynomial `Φ_0` is zero and all `ν_i(0)`
are zero. The first sum vanishes, and each Ramanujan factor is `p-1`.
The already proved ray identity `fourierSum_zero` gives
`C_p(0)=(p-1) projectiveTrace`. Cancelling the nonzero `p-1` proves

$$
\operatorname{projectiveTrace}=p\sum_i\chi_p(\kappa_i).
$$

This use of the ray identity needs only homogeneity of the actual
quadratic polynomial and the quadratic character's square being the
principal character. It does not call the Katz size estimate or the
elimination and Bertini constructions for exceptional planes.

`diagonal_projectiveQuadraticTrace_eq` transports the equality to the
existing integer-valued `projectiveQuadraticTrace` by the injective
integer-to-complex cast. That trace is the sum of the actual integer
quadratic character over the actual projective quadric. Its summand is
independent of representative because the polynomial is homogeneous of
degree two. Thus the trace endpoint is the source `a_p(G)`, not a new
quantity defined by the proposed answer.

## Arbitrary cubic sums and the generic bound

The generic integral condition is the literal nondivisibility of
`F*(u) * ∏ i, u_i`. `diagonalPencil_generic_reduction` reduces this
product into the prime field and proves every coordinate nonzero and
the actual dual quadratic value nonzero. `diagonalPencil_dual_map`
identifies that reduced value with the reduction of the integral
adjugate-polynomial evaluation. No extra assumption on the reduced
degree is imposed.

Nonzero coordinates make the singular-index filter empty. The dual
coefficient identity proves that `-Φ_u` has degree exactly three. The
proof now bounds its complete quadratic-character sum, treating its two
possible root behaviors separately.

### Three distinct geometric roots

If the cubic is separable, `weil_bound_of_separable` proves its geometric
root count from the library's root theorem over an algebraic closure and
applies the existing registered premise `Trusted.weil_simple_roots`.
Its hypotheses are checked: the actual quadratic character is
nonprincipal at the derived odd prime; the actual polynomial has positive
degree three; and its three geometric roots are distinct. The bound is
exactly `2 sqrt(p)`.

### Repeated roots

The repeated-root case is proved internally. A prime field is perfect,
so a nonseparable polynomial is not squarefree. An irreducible polynomial
`g` with `g² ∣ f` then exists. Since the actual degree is three,
`2 deg(g) ≤ 3` and irreducibility forces `deg(g)=1`. The remaining quotient
also has degree one. Writing the two linear factors explicitly gives

$$
f=C(c)(X-C(a))^2(X-C(b)),\qquad c\ne0,\quad a,b\in\mathbf F_p.
$$

The proof permits `a=b`, so it includes a triple root. This proves the
descent of the repeated root to the base field instead of assuming it.
It is an algebraic alternative to the source's gcd-and-derivative
argument and uses only proved perfect-field and polynomial-factorization
results from mathlib.

For `x ≠ a`, the nonzero square `(x-a)²` has quadratic character one.
The full character sum of the remaining translated linear expression is
zero. Removing the value at `x=a` proves the exact formula

$$
\sum_x\chi_p(c(x-a)^2(x-b))=-\chi_p(c(a-b)).
$$

When `a=b`, both sides vanish; otherwise the norm is at most one. This
matches both repeated-root cases in the source, after applying it to
`f=-Φ_u`. The argument does not invoke the Weil premise in this branch.
The already derived `p ≥ 5` gives the uniform bound `2 sqrt(p)` for both
branches.

Deleting the actual root set costs at most its cardinality because every
quadratic-character value has norm at most one. The cardinality bound
four gives `2 sqrt(p) + 4`. Multiplication by the actual outer factor `p`
in the exact pencil identity gives `2 p sqrt(p) + 4 p`. The existing
proved real-power identity converts this to

$$
\lVert C_p(u)\rVert\le 2p^{3/2}+4p.
$$

The endpoint applies to every cubic produced by the literal source
frequency condition; it has no separability, rational-root, or
squarefreeness hypothesis.

## Complete integral endpoint

The final declaration is `QuaternaryQuadraticForms.diagonal_pencil` in
`DiagonalPencilTheorem.lean`. Its data are

```lean
(p : ℕ) [Fact p.Prime]
(a b u : Fin 4 → ℤ)
(hp : ¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b)
```

There are no other coefficient, smoothness, degree, root, or
nonvanishing assumptions. Its three conjuncts are as follows.

| Source clause | Integral Lean endpoint and exact correspondence |
| --- | --- |
| `eq:exactpencil` for every `u ∈ ℤ⁴` | `integral_diagonal_fourier_pencil_formula` uses the existing `integralFourierSum`, the formal integer `diagonalPencilPhi` mapped into `ZMod p`, the complement of the actual reduced singular-root set, and a singular sum filtered by the literal integer divisibility `(p : ℤ) ∣ u i`. Its `κ_i` and `ν_i` arguments are reductions of the integer source expressions. |
| `eq:diagtrace` | `integral_diagonal_projectiveTrace_eq` is an equality in `ℤ` for the existing `integralProjectiveQuadraticTrace`, with right side `(p : ℤ) * ∑ i, quadraticChar (ZMod p) (κ_i mod p)`. |
| `eq:diagbound` under the source frequency condition | `integral_diagonal_fourier_bound` bounds the norm of the same `integralFourierSum` by `2 * (p : ℝ) ^ (3 / 2 : ℝ) + 4 * (p : ℝ)`, assuming only the additional literal nondivisibility displayed below. |

The frequency condition in the final theorem is

```lean
¬ (p : ℤ) ∣
  dotProduct u ((Matrix.diagonal a).adjugate.mulVec u) * ∏ i, u i
```

This is exactly `p ∤ F*(u) u_1 u_2 u_3 u_4`, using the source adjugate
definition. In the bundled `diagonal_pencil` result it appears as an
implication in the third conjunct; the first two conjuncts do not depend
on it. Thus every integral frequency has the exact identity, while only
the generic frequencies are subject to the smaller bound.

The wrapper unfolds the existing integral definitions and uses proved
maps of the actual diagonal matrix and quadratic polynomial. The
singular-index filter is rewritten using
`ZMod.intCast_zmod_eq_zero_iff_dvd`. The regular summand uses the mapped
formal integer polynomial, rather than a new prime-field polynomial with
an unproved correspondence. The trace proof maps the original integer
`κ_i` as well.

For source instances, `p ∤ 2 α M` lies in the domain `p ∤ N_G` of the
source trace by the completed Lemma 4.5. The finite trace identity here
uses its direct projective-sum definition and the ray identity; it does
not assume the trace formula or invoke a size estimate to define the
trace. The prime restriction itself implies nonzero integer `α` and `M`,
so no extra integral nonsingularity or pair-difference assumptions are
needed in this endpoint. Omitting the unused standing nonsquare condition
also broadens the result without excluding a source instance.

## Inspected dependencies and review conclusion

The actual `#check` types and `#print axioms` results of all 67 public
exports across the thirteen new modules were inspected after strict
compilation. The complete inspection finished successfully. Fifty-nine
exports have exactly

```text
Classical.choice
Quot.sound
propext
```

One further export, `diagonalPencilCoeff_map`, has only `propext`. The
remaining seven have the three standard foundations and exactly the one
existing literature premise

```text
QuaternaryQuadraticForms.Trusted.weil_simple_roots
```

Those seven are the three general cubic-bound exports
`quadraticChar_cubic_sum_norm_le`, `quadraticChar_cubic_sum_sdiff_norm_le`,
and `quadraticChar_cubic_sum_sdiff_four_norm_le`; the two prime-field
generic-bound exports `diagonal_fourier_generic_bound_sqrt` and
`diagonal_fourier_generic_bound`; the integral bound
`integral_diagonal_fourier_bound`; and the bundled `diagonal_pencil`.

In particular, both `integral_diagonal_fourier_pencil_formula` and
`integral_diagonal_projectiveTrace_eq` have foundations only. The
perfect-field factorization and exact repeated-root sum also have no
literature dependency. This verifies the separation between the exact
identities and the single existing input used for the separable cubic
estimate. No Bertini, Lang elimination, or projective Katz premise occurs
in these new exports.

The existing external interface and its exact source boundary are recorded
in [weil_input.md](weil_input.md). Neither the Gauss-sum facts already
proved by mathlib nor the elementary Ramanujan evaluations introduce an
additional trusted statement. No literature input was added or enlarged
for this lemma.

All thirteen new modules, including the complete integral wrapper, passed
compilation with the pinned Lean/mathlib revisions, `autoImplicit=false`,
and `warningAsError=true`. The inspected final type contains the source's
actual integral objects, the exact prime and frequency restrictions, and
all three source conclusions. The review finds no omitted clause,
strengthened hypothesis, dropped singular case, unjustified root-descent
assumption, or mathematical gap.

This completed source-correspondence review supports Certified
classification of Lemma 4.6 once the full repository verification gates
pass. The live ledger, verification report, and execution checkpoint
record those gates, the checked hashes and dependencies, and the exact
commit/run evidence. Completing Lemmas 4.5 and 4.6 proves the two local
identities used in Theorem 1.3; its remaining analytic conclusion and the
rest of the manuscript are separate obligations.
