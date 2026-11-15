# Source correspondence: the actual main coefficient and its uniform bound

## Completed mathematical scope

This record covers the frozen manuscript's auxiliary obligations
`aux:Sxi` and `aux:Sxibound`, equations `eq:Sxi` and `eq:Sxibound`
at lines 1515–1527. These are supplementary assertions, not new numbered
results. Their prerequisites `lem:crt`, `lem:density`, `lem:singseries`,
and `aux:Cfactor` were already Certified.

The source is the unchanged
[manuscript](../../manuscript/quadratic_character_sums_github.tex), SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

All implementation and independent mathematical correspondence reviews are
complete. Exact aggregate verification and publication evidence belong in
[CHECKPOINT.md](../../CHECKPOINT.md). No literature premise is added or used
by these coefficient deductions.

## Actual definition and exact local product

For the original functions supplied only at primes outside N, define

\[
\mathfrak S_\xi(q)
=\frac{C_q(0)}{q^3}\,\operatorname{singularSeriesValue}(q,A,0).
\]

The definition `sourceMainCoefficient` uses the literal
`sourceConstrainedFourierSum` and the existing increasing-modulus limit
of the coprime complete-sum partial sums. The conditionally convergent
series at zero shift is not replaced by an unordered `tsum`.

For symmetric nonsingular integral A with nonsquare determinant, the
original supplied character with its good-prime agreement, squarefree
positive q coprime to N, the radical condition rad(N_F)|N, and the
original scalar-invariance hypothesis on the local functions, the endpoint

`sourceMainCoefficient_eq_prime_product`

proves exactly

\[
\mathfrak S_\xi(q)
=\mathfrak S_F\prod_{p\mid q}\frac{C_p(0)}{p^3\sigma_p}.
\]

The proof combines the already checked source Fourier prime factorization
and `singularSeriesValue_zero_eq`. A finite subtype reindexing identifies
the two prime-index conventions. Squarefreeness supplies
\(\prod_{p\mid q}p=q\). There is no additional convergence premise.

The empty-product case is explicit:
`sourceMainCoefficient_one_eq_singularSeriesConstant` gives
\(\mathfrak S_\xi(1)=\mathfrak S_F\).

## Exact local estimates

The actual good-prime density is positive and its reciprocal has norm at
most two. This follows internally from the certified formula

\[
\sigma_p=\frac{1-\chi(p)/p^2}{1-\chi(p)/p}
\]

and the certified Legendre norm bound. For p≥2, the numerator of the
reciprocal has norm at most 3/2, while its denominator has norm at least
3/4. The real inequality \(\sigma_p^{-1}\le2\) is also exported.

At frequency zero, the literal Fourier-stratum hypothesis implies
\(|C_p(0)|\le2Kp^2\). The proof bounds the exceptional indicator by one;
it makes no assumption that the polynomial vanishes at zero.

Combining these yields the actual local factor bound

\[
\left|\frac{C_p(0)}{p^3\sigma_p}\right|\le\frac{4K}{p}.
\]

All factors use the original source functions. Coprimality and the radical
condition establish that each prime is good before the density formula is
applied.

## Uniform global bounds and boundary cases

`sourceMainCoefficient_norm_le` proves

\[
|\mathfrak S_\xi(q)|
\le|\mathfrak S_F|\frac{(4K)^{\omega(q)}}q.
\]

`source_main_coefficient_bound` retains that exact bound and proves

\[
\exists C_{A,K,\varepsilon}>0,\qquad
|\mathfrak S_\xi(q)|\le C_{A,K,\varepsilon}q^{-1+\varepsilon}.
\]

The quantifier order is literal: A,K,epsilon precede C; C precedes the
character level M, the character chi, N, every source local function,
every exceptional polynomial, and q. The internally proved
`primeFactor_pow_le_rpow` handles the prime-factor count.

To make the dependence independent of the supplied character,
`singularSeriesConstant_eq_orderedValue` identifies every admissible
source constant with `singularSeriesValue 1 A 0`. If B>0 is the constant
in the prime-factor subpower bound, the proof selects

\[
C=(|\operatorname{singularSeriesValue}(1,A,0)|+1)B.
\]

This remains strictly positive when the singular-series constant is zero.
The proof never divides by that global constant and covers q=1.

The final source endpoint assumes the original full Fourier bound and
specializes it at the zero integer vector. Degree bounds, polynomial
nonvanishing, the local weight's value at zero, its pointwise norm bound,
and N≥1 are not used by these deductions; omitting them gives a stronger
valid statement. Scalar invariance remains where the actual Fourier
factorization requires it.

## Implemented files

| Module | Scope |
| --- | --- |
| [SourceMainCoefficient.lean](../../QuaternaryQuadraticForms/SourceMainCoefficient.lean) | Actual definition, finite prime reindexing, exact product, modulus one, independence of the admissible character |
| [MainCoefficientLocalBounds.lean](../../QuaternaryQuadraticForms/MainCoefficientLocalBounds.lean) | Actual density positivity and reciprocal bound, zero-frequency stratum estimate, local factor bound |
| [SourceMainCoefficientBound.lean](../../QuaternaryQuadraticForms/SourceMainCoefficientBound.lean) | Explicit finite-product bound and the complete uniformly quantified source endpoint |

There are fourteen new public theorem exports in these three modules.
Their proofs use only the standard logical foundations and already checked
internal prerequisites. No analytic estimate from Lemma 2.2 is used by
these coefficient identities.

