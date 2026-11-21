# Lemma 5.2: bounded off-cone reduction and scale estimates

## Scope of this supporting batch

This record covers six supporting exports in two exact supplied modules:
`OffConeFrequencyReduction.lean` (130 lines) and
`OffConeFrequencyScales.lean` (91 lines). The source calculation is at
lines 2148–2180 of `manuscript/quadratic_character_sums_github.tex`.
Its SHA-256 remains
`e3cd28b361ec143d043d4d9ced55939c234648f73f23a05377af4aaefa98b49a`.

Lemma 5.2 remains **Partial**. Its large-frequency clause was completed in
the [previous checkpoint](large_frequency_truncation.md). The present
batch supplies reductions used in the bounded off-cone clause; it does
not establish that clause's final normalized `O((Bq)^(1+8 eta))` bound.
The arithmetic averaging, final exponent assembly, and complete source
endpoint remain pending. No numbered or auxiliary status is promoted.

## Exact arithmetic objects and cutoffs

`mem_offConeFrequencies` proves that the finite frequency set is exactly
`0 < norm(u) <= U` with `integralQuadraticValue A.adjugate u != 0`.
The norm is the Euclidean norm of the integral frequency vector. The
positive lower bound excludes a zero denominator in every reciprocal
norm. The dual quadratic form is the manuscript's actual integral form.

`sourceMixedCompleteSum_sum_le_gcd_classes` retains the original
prime-weight functions and mixed complete sum. It first identifies their
existing total-family representation, enlarges the strict positive-modulus
cutoff `c < X` to `1 <= c <= floor(X)`, and then partitions by `gcd(c,q)`.
The enlargement is justified by nonnegative summands. Integer cutoff
endpoints, `q = 1`, and empty cutoff ranges are included; squarefreeness
is unnecessary for this identity and inequality.

## Scaled integral reduction

`ScaledFrequencyIntegralBound.offCone_modulus_reduction` uses the actual
integral at scale `c/Q` and frequency `u/sqrt(q)`, with
`Q = B/sqrt(q)` and `U = sqrt(q)*B^eta`. Equation (5.5) is an explicit
hypothesis, available from the already certified `aux:Ipiece` endpoint.
The derivative term is nonnegative, so it may be dropped. Multiplication
by `c^(-4)` gives

\[
 \left|\sum_{c<X}\sum_{u\in\mathcal U}
 c^{-4}\mathcal S_{q,c}(u)I^*_{c/Q}(u/\sqrt q;w)\right|
 \le J\frac qB B^{3\eta}
 \sum_{d\mid q}\sum_{u\in\mathcal U}
 \frac{\operatorname{modulusNormSum}(q,d,u,X)}{\lVert u\rVert},
\]

where `mathcal U` denotes the exact bounded off-cone set above, and
`modulusNormSum` is the existing sum of `|S_(q,c)(u)|/c^3` over the inclusive
modulus range and its gcd class. The constant `J` precedes the varying
arithmetic data, `B`, `X`, and the individual weight. This is the sum
**before multiplication by the Poisson prefactor**. That normalization
is deliberately reserved for the subsequent assembly.

## Dual-form growth and average scales

`dualQuadraticValue_ball_bound` gives `|F*(u)| <= M U^2`, where the
positive constant `M` depends only on the fixed matrix. Applying it with
`U = sqrt(q)*B^eta`, the theorem `offCone_dual_growth` proves

\[
 (r_0Q|F^*(u)|)^\eta
 \le (r_0M)^\eta(Bq)^{2\eta}.
\]

The assumptions are `r_0 >= 1`, `B,q >= 1`, and `0 < eta <= 1/4`.
The proof uses `U^2 <= qB`, `r_0 Q <= r_0 B`, and `q <= q^2`.
The constant is uniform in `B`, `q`, and `u`.

For `q = de`, the sixth export `offCone_average_scale` proves

\[
 d^2e^{3/2}\left(\frac{U^3}{d}+e^{1/2}U^2\right)
 \le 2q^3B^{3\eta}.
\]

It retains the factor `d^2` from the modulus estimate. The first term
uses `d >= 1`; the second uses `B^(2 eta) <= B^(3 eta)`.
The boundary `d = e = B = 1`, `eta = 0`, is included. This is the
scale calculation needed after applying Lemma 3.11, not the arithmetic
application of that lemma itself.

## Audit and reproducibility

Independent source review found no required fatal, serious, moderate, or
light correction in these six exports. The supplied records assign only
`Classical.choice`, `Quot.sound`, and `propext` to every export. No
literature premise is added. In particular, the analytic bound in the
reduction remains an explicit hypothesis supplied by a certified
predecessor; it is not introduced as an axiom.

The exact extracted package records and original report identity are in
[offcone_reduction_package_evidence.json](../local/offcone_reduction_package_evidence.json).
Fresh execution is performed by `python3 scripts/verify_offcone_reduction.py`
with the pinned dependencies and official mathlib cache. It checks the
exact supplied bytes, strict compilation, declaration kinds, all six
actual theorem types and axiom sets, the loaded project axiom registry,
and dependency revisions. This review itself is included in the focused
report's input hashes. The exact run, checked commit, preserved report,
and acceptance decision are recorded in [CHECKPOINT.md](../../CHECKPOINT.md).
