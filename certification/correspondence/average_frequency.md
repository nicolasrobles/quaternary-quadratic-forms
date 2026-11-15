# Source correspondence: Lemma 3.11 and the complete-sum factorization

## Scope and frozen source

This record covers the complete assertion of `lem:average`, Lemma 3.11,
and the separate supplementary obligation `aux:Cfactor`. The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The manuscript and its PDF are unchanged.

| Source location | Reviewed content |
| --- | --- |
| Lines 155–160, 814–819 | Symmetric nonsingular integral matrix and the actual adjugate dual form |
| Lines 562–563 | Euclidean norm convention |
| Lines 997–1022 | Source modulus, supplied good-prime functions and polynomials, degree bound, scalar invariance, and the local stratified Fourier bound |
| Lines 1089–1090 | Prime factorization of `C_q(u)` and multiplicativity of `S_c(u)` |
| Lines 1534–1536 | Original product indicator `Delta_h(u)` and its empty-product convention |
| Lines 1539–1567 | Both already proved bounds of Lemma 3.10 |
| Lines 1569–1576 | Complete Lemma 3.11 and equation (3.31) |
| Lines 1578–1591 | Actual Fourier-product expansion, divisor average, and epsilon absorption |

The final numbered-result endpoint is `source_average_frequency_bound` in
[SourceAverageFrequencyTheorem.lean](../../QuaternaryQuadraticForms/SourceAverageFrequencyTheorem.lean).
The exact factorization obligation uses
`sourceConstrainedFourierSum_primeFactors` together with the previously
checked `unweightedCompleteSum_mul`. The latter theorem is reused without
changing its proof or its existing export record.

## Statement and actual objects

The final source theorem proves

\[
\sum_{\substack{0<\|u\|\le U\\q_1\mid F^*(u)}}
 \frac{|C_{q_2}(u)|}{\|u\|}
\le C_{E,K,\varepsilon}q^\varepsilon q_2^{3/2}
 \left(\frac{U^3}{q_1}+q_2^{1/2}U^2\right).
\]

| Manuscript object | Lean representation |
| --- | --- |
| `F*(u)` | The actual integer `dotProduct u (A.adjugate.mulVec u)` |
| `norm(u)` | `integerEuclideanNorm u`, the standard Euclidean norm of the real-cast integer vector |
| `0 < norm(u) <= U`, `q1 | F*(u)` | Exact membership in `divisibleEuclideanBall A q1 U`, proved in the Lemma 3.10 modules |
| Original functions at good primes | `ξ : ∀ p, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → Complex` |
| Original polynomials at good primes | `D : ∀ p, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)` |
| `C_q(u)` | `sourceConstrainedFourierSum N ξ q hqN A u`, a literal finite sum with `sourceCompositeWeight` |
| `Delta_h(u)` | The product of the original polynomial zero indicators, transported exactly through `exceptionalIndicator_extend` |
| `q=q1*q2` | An explicit equality in the final theorem |
| Positive moduli | `NeZero` instances for natural moduli, equivalent to positivity |
| Prime to excluded primes | The literal `q.Coprime N` and `primeRadical (quadraticBadPrimeModulus A) ∣ N` |

The new source Fourier-sum definition uses the original supplied weight
product directly. The theorem `constrainedFourierSum_extend_eq_source`
identifies it with the earlier constrained sum. At a prime,
`sourceConstrainedFourierSum_prime` identifies it with the actual
finite-field Fourier transform on the quadratic cone. Thus the local
hypothesis in the final theorem is precisely equation (3.3), not a bound
for a different or abstractly supplied numerical function.

The final theorem receives the source's squarefreeness of `q`, its
factorization, and its coprimality to `N`. It derives squarefreeness of
both factors, their mutual coprimality, and every coprimality condition
needed at a divisor `h` of `q2`. These are not additional hypotheses.

## Quantifiers and permissible strengthening

For every real `E >= 1`, real `K >= 1`, and `epsilon > 0`, the final
theorem chooses one positive constant before the matrix, the excluded
modulus, the polynomial family, the weight family, the factorization,
and the real radius `U >= 1`. Its only allowed dependence is therefore
on `E,K,epsilon`. In particular it is independent of all coefficients,
all moduli, the choice of local functions, and the frequency radius.

The real degree bound is converted internally to `Nat.ceil E`, just as
in Lemma 3.10. No integer-degree-bound hypothesis survives in the final
endpoint. The matrix may vary after the constant is chosen; this is a
valid strengthening of the source's fixed-matrix setting.

The source's nonzero-scalar invariance and local stratified estimate are
used. The conditions `ξ_p(0)=0` and `norm(ξ_p(x))<=1` are unnecessary for
this deduction once that estimate is supplied. The global nonsquare
determinant condition is likewise unnecessary: only symmetry and
nonsingularity enter the congruence count. Their omission is a proved
strengthening, not an assumed replacement conclusion.

The Fourier estimate is an explicit hypothesis of the abstract Section 3
argument. Lemma 4.4 supplies it later for polynomial-character weights;
it is not inserted here as an extra literature premise or as an artificial
dependency of the abstract theorem.

## Exact factorization and exceptional-divisor expansion

The already checked CRT theorem proves

\[
C_{q_2}(u)=\prod_{p\mid q_2}C_p(u).
\]

The source-domain wrapper retains the original supplied functions in
every factor. The other clause of `aux:Cfactor`,

\[
S_{c_1c_2}(u)=S_{c_1}(u)S_{c_2}(u)\qquad ((c_1,c_2)=1),
\]

is the previously checked `unweightedCompleteSum_mul`, for arbitrary
positive coprime moduli, including bad primes and modulus one.

For the exceptional-factor expansion, actual divisors of a positive
squarefree modulus are put in bijection with subsets of its prime
divisors. The maps are the prime-factor set and the product of its
members. Their inverseness is proved with the existing natural-number
prime-factorization theorems. The empty subset corresponds to one.

The finite product expansion then gives the exact identity

\[
\prod_{p\mid q_2}\bigl(1+p^{1/2}\mathbf1_{D_p(u)=0}\bigr)
=\sum_{h\mid q_2}h^{1/2}\Delta_h(u).
\]

Factoring out `K*p^(3/2)` from each local majorant and using squarefreeness
proves equation (3.32) for the actual Fourier sum:

\[
|C_{q_2}(u)|\le K^{\omega(q_2)}q_2^{3/2}
 \sum_{h\mid q_2}h^{1/2}\Delta_h(u).
\]

The CRT identity and this divisor expansion are deductions. Neither is
left as a premise in the final numbered-result endpoint.

## Divisor summation and exponent allocation

The proof first inserts the pointwise bound into the literal finite
Euclidean sum and interchanges two finite sums. Lemma 3.10 applies to
each `h|q2`: the squarefree factorization implies that `q1,h` are
positive, squarefree, mutually coprime, and that `q1*h` is prime to `N`.

Put `eta=epsilon/3`. Lemma 3.10 gives a common constant `B` with

\[
\sum_{\substack{0<\|u\|\le U\\q_1\mid F^*(u)}}
 \frac{\Delta_h(u)}{\|u\|}
\le B(q_1h)^\eta\left(\frac{U^3}{q_1h}+U^2\right).
\]

Since `1<=h<=q2`, each divisor contributes at most

\[
h^{1/2}\left(\frac{U^3}{q_1h}+U^2\right)
\le \frac{U^3}{q_1}+q_2^{1/2}U^2.
\]

Also `(q1*h)^eta <= q^eta`. The separately proved fixed-base and divisor
estimates give

\[
K^{\omega(q_2)}\le C_1q_2^\eta\le C_1q^\eta,
\qquad
\tau(q_2)\le C_2q_2^\eta\le C_2q^\eta.
\]

The product of the three small-power factors is exactly `q^epsilon`.
The final constant is `B*C1*C2`, which is positive and is chosen before
all varying source data. No extra logarithm or extra epsilon power is
hidden in the endpoint.

## Modules and public interfaces

The milestone adds fourteen public theorem exports in six modules.

| Module | New exports | Role |
| --- | ---: | --- |
| [FourierDivisorExpansion.lean](../../QuaternaryQuadraticForms/FourierDivisorExpansion.lean) | 2 | Exact squarefree-divisor reindexing and exceptional-indicator product expansion |
| [FourierProductBound.lean](../../QuaternaryQuadraticForms/FourierProductBound.lean) | 2 | Exact local-majorant product and actual Fourier norm bound |
| [ExceptionalDivisorSum.lean](../../QuaternaryQuadraticForms/ExceptionalDivisorSum.lean) | 3 | Per-divisor shape estimate, uniform divisor summation, and weighted finite-sum interchange |
| [AverageFrequencyBound.lean](../../QuaternaryQuadraticForms/AverageFrequencyBound.lean) | 1 | Uniform average from the pointwise divisor majorant, with the exact epsilon budget |
| [SourceFourierSums.lean](../../QuaternaryQuadraticForms/SourceFourierSums.lean) | 4 | Literal original source sum, its internal and prime-field bridges, modulus one, and exact prime product |
| [SourceAverageFrequencyTheorem.lean](../../QuaternaryQuadraticForms/SourceAverageFrequencyTheorem.lean) | 2 | Complete natural-degree and real-degree source endpoints |

The generic finite-sum helper permits an arbitrary real-valued function
with a pointwise majorant. This is only an intermediate interface. The
final source theorem specializes it to the norm of the actual source
Fourier sum and proves the majorant from CRT and the explicit local
hypothesis.

## Boundary cases and trust boundary

- `q2=1`: the Fourier sum is one, the divisor set is `{1}`, and the
  exceptional indicator is the empty product one.
- `q1=1`: every integral dual value is divisible by it.
- `q=q1=q2=1`: the source estimate reduces to the corresponding finite
  inverse-Euclidean-norm lattice estimate.
- The frequency zero is excluded by exact positive-norm membership;
  all nonzero frequencies on or off the dual cone are included.
- Nonintegral radii, `U=1`, real degree bounds, nonzero constant prime
  polynomials, and independent coefficients at different primes are allowed.
- No condition `D_p(0)=0` and no extra characteristic-versus-degree
  restriction are imposed.

No new literature input is introduced or used in this milestone. The
previously registered four literature declarations remain unchanged.
Actual declaration kinds, complete types, and axiom dependencies are
checked by the project verifier; successful execution and exact-commit
CI evidence are recorded in [CHECKPOINT.md](../../CHECKPOINT.md).
This mathematical correspondence review is separate from those execution
checks. No claim about the later analytic proposition or the main
theorems follows merely from this milestone.
