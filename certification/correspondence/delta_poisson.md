# Source correspondence: the delta–Poisson identity (Lemma 5.1)

## Scope and source locations

This record covers the complete statement `lem:poisson`, Lemma 5.1, in
the frozen manuscript
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex).
The statement and equation (5.3) are at lines 2045–2054; the proof is at
lines 2056–2089. The manuscript SHA-256 is
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

The complete endpoint is
`QuaternaryQuadraticForms.source_delta_poisson` in
[PoissonTheorem.lean](../../QuaternaryQuadraticForms/PoissonTheorem.lean).
Independent source correspondence review found no mismatch in the objects,
hypotheses, normalization, signs, finiteness, or convergence clauses. The
compiled endpoint was independently inspected under
`warningAsError=true` and `autoImplicit=false`: it is a proved theorem,
its actual type contains all four clauses reviewed below, and its axiom
profile contains exactly the two registered literature inputs and three
standard foundational axioms listed at the end of this record. The
aggregate verification state and exact publication evidence are recorded
separately in [CHECKPOINT.md](../../CHECKPOINT.md).

This milestone proves the exact transformation in Lemma 5.1. Proposition
5.1 (`prop:analytic`), immediately preceding the lemma, is the subsequent
asymptotic formula and is not claimed here.

## Mathematical statement and source assumptions

Let `A` be the integral coefficient matrix, put `F(x)=x^T A x`, and let
`w: R^4 -> C` be infinitely differentiable with compact support. For
`q>=1` coprime to `N`, set `Q=B/sqrt(q)` and assume `B>0` and `Q>=3`.
Using the original supplied good-prime functions, define

\[
\xi_q(x)=\prod_{p\mid q}\xi_p(x\bmod p),\qquad
T_q(B;w)=\sum_{\substack{x\in\mathbb Z^4\\F(x)=0}}
 w(x/B)\xi_q(x).
\]

The implemented identity is exactly

\[
T_q(B;w)=c_Q\frac{B^2}{q^3}
 \sum_{c\ge1}c^{-4}\sum_{u\in\mathbb Z^4}
 \mathcal S_{q,c}(u)
 I_{c/Q}^*\left(\frac{u}{\sqrt q};w\right).
\]

It includes finite support of the positive-modulus terms and absolute
convergence of every frequency series. The theorem also proves finite
support of the original weighted lattice sum. The hypothesis `Q>=3`
is explicit; the proof uses the previously certified normalized delta
identity only in that range.

The source asks that `q` be squarefree and that the global arithmetic
and local-weight hypotheses of Section 3 hold. The Lean theorem is valid
for every positive natural `q`, encoded by `[NeZero q]`, with
`q.Coprime N`, and every integral `4 x 4` matrix `A`. No symmetry,
nonsingularity, determinant condition, local Fourier estimate, scalar
invariance, or pointwise bound on the prime weights is needed for this
exact identity. These are valid generalizations: integrality permits
the delta insertion, homogeneity gives the scaling, and the product over
distinct prime divisors is periodic modulo `q` even when `q` is not
squarefree. Specialization to the manuscript assumptions is immediate.

The weight hypothesis is exactly smoothness and compact support as defined
at manuscript lines 641–643. There is no annular-support or nonvanishing-
gradient hypothesis. The support may contain the origin, and the zero
lattice point and zero frequency are retained. No singular integral or
estimate from Lemma 2.2 is needed for this transformation.

## Literal object correspondence

| Source object | Lean object and interpretation |
| --- | --- |
| `R^4` | `RealVector4 = EuclideanSpace ℝ (Fin 4)` |
| `Z^4` | `Fin 4 → ℤ`, embedded coordinatewise by `integerRealVector` |
| `F(x)=x^T A x` on integers | `integralQuadraticValue A x` |
| The same real quadratic form | `realQuadraticValue (A.map (Int.castRingHom ℝ))` |
| A smooth compactly supported weight | `IsSmoothWeight w` |
| `h` and `c_Q` from Lemma 2.1 | The fixed definitions `heathBrownDeltaKernel` and `heathBrownNormalization` |
| The supplied functions at primes not dividing `N` | `ξ : ∀ p, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ` |
| `xi_q` | `sourceCompositeWeight N ξ q hqN`, the literal product over `q.primeFactors` |
| `T_q(B;w)`, equation (5.1) | `sourceQuadraticZeroSum N ξ q hqN A B w` |
| `g_c(x)` in the proof | `poissonTestFunction A B Q w c x` |
| `S_{q,c}(u)`, equation (3.4), label `eq:Snewdef` | `sourceMixedCompleteSum N ξ q hqN c A u` |
| `I_r^*(v;w)`, equation (2.2), label `eq:Istar` | `deltaIntegral F w r v` |
| Positive modulus `c>=1` | `c : ℕ+`; the modulus-one term is included |
| All integer frequencies | `u : Fin 4 → ℤ`, including `u=0` |

The mixed complete sum is the actual finite sum over `(ZMod c)ˣ` and
`Fin 4 → ZMod (q*c)`, with the condition `q | F(z)`, the original
prime-product weight, and the phase
`exp(2*pi*i*(a*F(z)+u·z)/(q*c))`. Canonical integer lifts define this
finite sum. The existing lift-independence theorems prove that changing
those representatives changes neither the condition nor the summand.
The unit group at `c=1` and the empty prime product at `q=1` are included
without a separate exclusion.

The internal total family `extendPrimeWeights N ξ` is only a representation
used by previously defined complete sums. The proved equalities
`compositeWeight_extend_eq_source`,
`weightedQuadraticZeroSum_extend_eq_source`, and
`mixedCompleteSum_extend_eq_source` identify both sides with the original
supplied functions. The final statement contains the source objects on
both sides; it assumes no values at unavailable primes.

The integral is the actual complex Bochner integral with the canonical
Euclidean Lebesgue measure. In the pinned mathlib,
`EuclideanSpace.volume_preserving_measurableEquiv` and
`PiLp.volume_preserving_toLp` identify this measure with coordinate product
Lebesgue measure. Thus the implementation agrees with the source's
fourfold integral, including its normalization.

## Clause-by-clause verification

The final theorem returns the following four conclusions in order.

1. The actual weighted zero-locus lattice summand has finite support.
   `scaledWeight_integerRealVector_finite` proves finiteness from compact
   support after the invertible scaling by `B`. Restricting to `F(x)=0`
   and multiplying by the arithmetic weight preserves it. Consequently
   the left `tsum` is the ordinary finite sum in the manuscript.
2. The displayed delta–Poisson identity holds with coefficient
   `((heathBrownNormalization Q * B^2 / q^3 : ℝ) : ℂ)`.
   The positive-index outer sum and all integer frequencies are literal;
   neither is replaced by an abstract candidate expression.
3. The function of `c : ℕ+` given by the entire
   `c^(-4)`-weighted frequency series has finite support.
4. For every positive `c`, the function of `u : ℤ^4` given by the norm
   of `sourceMixedCompleteSum * deltaIntegral` is summable. This is
   absolute convergence of the exact frequency series, for every modulus
   and hence in particular for every contributing modulus.

The internal cutoff is stronger than cancellation of an outer term.
`poissonTestFunction_eventually_zero` selects one natural `K` before
the Euclidean variable, and `poissonDeltaIntegral_eventually_zero`
selects one `K` before every frequency, such that `c>K` makes the whole
test function, respectively every actual integral, zero. If `M` bounds
`|F|` on the compact support of `w`, one may take

\[
K=\left\lceil Q\max\{1,2M\}\right\rceil.
\]

The proof uses the kernel support clause of Lemma 2.1 and handles the
zero weight as well. The manuscript's sufficient cutoff
`c/Q>1+2*max|F|` is weaker than this bound. No compactness assertion
about the nonclosed set of nonzero values is required: the bound is
obtained on the topological support.

## Internal deductions and normalization audit

`weightedQuadraticZeroSum_delta` applies the certified delta identity
to the integer `n=F(x)/q` when `q | F(x)`. The proof uses an actual
integer witness for divisibility and proves both
`n/Q^2=F(x/B)` and equality of the additive characters. Outside that
congruence the summand is zero. Finite lattice support and the existing
finite-support delta theorem justify the interchange of the lattice
and positive-modulus sums.

`poissonTestFunction_isSmoothWeight` proves smoothness by composition
with the quadratic form and the kernel on its positive first-coordinate
domain. Compact support comes from the scaled original weight. This is
proved for the actual `g_c`, before applying classical Poisson summation.

The residue-class modules construct an explicit quotient/remainder
equivalence between the integer lattice and a residue vector modulo
`q*c` together with an integer lattice vector. Periodicity of the actual
arithmetic summands, finite support on the lattice, and absolute
summability justify the reindexing and all exchanges with finite residue
and unit sums. `poisson_mixed_fourier_coefficient` identifies the result
with the already defined mixed complete sum, with its positive phase.

The Fourier transform is defined using `exp(-2*pi*i*<v,x>)`. The
general affine-lattice formula at spacing `q*c` has positive translation
phase and factor `(q*c)^(-4)`. The theorem
`poisson_affine_phase_eq_stdAddChar` proves the exact equality with
the standard additive character on `ZMod (q*c)`, including the inner
product, real casts, and sign.

`poissonFourierIntegral_testFunction` proves the substitution `x=B*y`
for the actual integral. The four-dimensional Jacobian is `B^4`, and
the resulting frequency identity is

\[
\frac{c}{Q}\,B\,\frac{1}{qc}=\frac1{\sqrt q}.
\]

Thus the Fourier integral is exactly
`B^4 * I_(c/Q)^*(u/sqrt(q);w)`. The proof uses the canonical Haar
change-of-variables theorem and proves positivity and nonvanishing of
all required scales. `poisson_normalization_factor` then proves
`B^4 * Q^(-2) * q^(-4) = B^2 * q^(-3)` with `Q=B/sqrt(q)`.
These factors are not absorbed into the definitions of the weight,
complete sum, or delta integral.

Absolute convergence first applies to the Fourier transform of `g_c`
at every fixed positive lattice spacing. Finite arithmetic sums preserve
it. Dividing by the nonzero scalar `B^4` gives precisely the norm
summability asserted for the final `S_{q,c}(u) * I_(c/Q)^*(u/sqrt(q);w)`
series. No quantitative decay constant uniform in `c`, `q`, `B`, or
the supplied prime weights is claimed or needed.

## The two literature dependencies

The nonlogical literature premises for this result are exactly:

| Registered declaration | Scope used here |
| --- | --- |
| `QuaternaryQuadraticForms.Trusted.heathBrown_delta_data` (`EXT.HB_DELTA`) | The previously registered fixed Heath–Brown bump/kernel construction, whose internal consequences include the normalized delta identity for `Q>=3`, joint smoothness, and kernel support |
| `QuaternaryQuadraticForms.Trusted.poisson_four_dimensional` (`EXT.POISSON_R4`) | The preregistered general affine-lattice Poisson formula for a smooth compactly supported complex function on `R^4`, with absolute convergence |

The delta construction and its normalization are reviewed in
[delta_symbol.md](delta_symbol.md). The precise Poisson interface,
preregistration, and normalization are reviewed in
[poisson_summation.md](poisson_summation.md). The shared primary reference
is D. R. Heath-Brown, *A new form of the circle method, and its application
to quadratic forms*, J. reine angew. Math. **481** (1996), 149–206,
[DOI](https://doi.org/10.1515/crll.1996.481.149),
[author PDF](https://ora.ox.ac.uk/objects/uuid%3Abbd3c62f-f010-44b5-8be5-87e903fb0084/files/m7ec02df6e1b8303a66e7a6015ecb6044).

The indexed primary PDF text on author pages 19–20 was independently
inspected. In the proof of Theorem 2, it states the general
n-dimensional formula for arbitrary smooth compactly supported `f`,
with negative Fourier sign; substituting `x=b+q*y` gives the positive
translation phase and `q^(-n)`. Specializing to dimension four gives
the registered normalization. Complex values follow by linearity, and
general real positive spacing and real translation follow from the
same affine change of variables. The absolute-convergence clause is
the standard consequence of rapid Fourier decay for smooth compact
support; those pages do not separately display it as an additional
theorem clause. The registration records that distinction explicitly.
No claim of visual PDF inspection is made.

Neither premise contains the manuscript's mixed complete sum, source
weight family, counting function, or delta–Poisson conclusion. The
specific test-function regularity, all finite-support assertions,
residue reindexing, character identification, integral scaling,
normalization, and complete source assembly are internal Lean proofs.
The only remaining foundational dependencies are Lean/mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound`.

