# Complete source correspondence for Lemma 5.2

## Scope and source

This review covers both clauses of Lemma 5.2: the normalized large-frequency
contribution is `O(1)`, and the normalized bounded off-cone contribution is
`O((Bq)^(1+8 eta))`. The frozen statement is at lines 2126–2130 of
`manuscript/quadratic_character_sums_github.tex`, its setup at lines
2091–2124, and its proof at lines 2132–2180. The source SHA-256 is
`e3cd28b361ec143d043d4d9ced55939c234648f73f23a05377af4aaefa98b49a`.

The new batch consists of three exact supplied modules, totaling 247 lines:

| Module | Lines | Role |
| --- | ---: | --- |
| [FrequencySourceData.lean](../../QuaternaryQuadraticForms/FrequencySourceData.lean) | 26 | The original arithmetic hypotheses |
| [OffConeModulusAverage.lean](../../QuaternaryQuadraticForms/OffConeModulusAverage.lean) | 123 | One public theorem applying the modulus and frequency-average estimates |
| [OffConeFrequencyTheorem.lean](../../QuaternaryQuadraticForms/OffConeFrequencyTheorem.lean) | 98 | Two public theorems giving the normalized bound and complete source endpoint |

The earlier [large-frequency review](large_frequency_truncation.md) and
[off-cone reduction review](offcone_reduction.md) remain part of the evidence.
No other numbered or auxiliary result is advanced by this batch.

## The arithmetic data are the manuscript's hypotheses

`FrequencySourceData A E K` packages the setup of Section 3, lines 997–1025:
`N >= 1`, `rad(N_F)` dividing `N`, nonzero exceptional polynomials `D_p`
of degree at most `E`, and the original prime weights. Their zero value,
norm bound and invariance under nonzero scalars are exactly (3.1).
The bound on the actual constrained Fourier sum is (3.3), with the same
constant `K` and the same exceptional-polynomial zero condition.

These are explicit source hypotheses. The structure adds no assumption
that the target conclusion holds, and the Fourier estimate is not installed
as a literature axiom. The form is symmetric and nonsingular; `E,K >= 1`,
squarefree `q >= 1`, `(q,N) = 1`, `B >= 9`, `q <= B`, and
`0 < eta <= 1/4` retain their source roles.

## Averaging the actual modulus sums

`source_offCone_modulus_average` applies the certified Lemmas 3.6 and 3.11.
For every divisor `d` of `q`, it sets `e = q/d`, proves positivity and
`q = de`, and supplies the required squarefreeness and coprimality data.
The original prime functions are transported by the previously proved
source-to-total-family identities, without changing the complete sums.

The private restriction lemma retains the indicator `d` dividing `F*(u)`.
It enlarges the bounded off-cone set to the corresponding divisible
Euclidean ball only after passing to nonnegative norm summands. In
particular, the factor `d^2` from Lemma 3.6 is preserved.

The average estimate contributes one factor `q^eta`; summing over all
divisors of `q` contributes a second via the certified divisor bound.
The resulting estimate is

\[
 \sum_{d\mid q}\sum_{u\in\mathcal U}
 \frac{\operatorname{modulusNormSum}(q,d,u,r_0Q)}{\lVert u\rVert}
 \le C(Bq)^{2\eta}q^3B^{3\eta}q^{2\eta},
\]

where `mathcal U` is the exact set `0 < norm(u) <= sqrt(q)*B^eta`,
`F*(u) != 0`, and `modulusNormSum` is the actual previously defined
gcd-restricted sum of `|S_(q,c)(u)|/c^3`. The constant precedes the data
`N,D_p,xi_p,q,B`. The cases `q = 1`, `d = 1`, and `e = 1` are included.

## The actual Poisson normalization and final exponent

`ScaledFrequencyIntegralBound.boundedOffCone` uses the original finite
bounded off-cone sum with its strict positive-modulus cutoff `c < r_0 Q`
and the actual coefficient `c_Q B^2/q^3`. From `B >= 9` and `q <= B` it
derives `Q = B/sqrt(q) >= 3`, and the existing normalization theorem gives
`0 < c_Q <= H+1` with a uniform constant.

Combining that coefficient, the already checked integral reduction, and
the arithmetic average gives

\[
 C\,Bq(Bq)^{2\eta}B^{6\eta}q^{2\eta}
 \le C(Bq)^{1+8\eta}.
\]

The final absorption is exactly `q^(2 eta) <= q^(6 eta)`, valid for
`q >= 1` and positive `eta`. All products, powers, and nonzero
denominators are handled internally. The resulting constant is chosen
before the individual source data, modulus, scale, and localized weight.

## One common localization gives both clauses

The final export `source_offcone` obtains a single positive `delta <= 1`
and cutoff `r_0 >= 1` from the certified `source_delta_integrals`.
These are chosen before `E,K,eta` and all varying arithmetic data.
The integral vanishes for `r >= r_0` for every actual localized piece.

On the exact localized weight family whose closed support meets `F = 0`,
the endpoint returns both `LargeFrequencyBound` and `BoundedOffConeBound`
with this same `delta,r_0`. The first is the complete normalized `O(1)`
tail; the second is the complete normalized `O((Bq)^(1+8 eta))` estimate.
Thus the source endpoint covers every clause of Lemma 5.2, with the
uniformity stipulated immediately before the lemma.

## Audit, dependencies and execution

Independent source review approved all three exports and the arithmetic
data definition, with no required fatal, serious, moderate, or light
correction. The averaging theorem uses only standard logical foundations.
The normalization theorem additionally uses the existing delta-construction
premise; the complete source endpoint uses the same seven already
registered analytic premises. No literature premise is added.

The [extracted package evidence](../local/offcone_completion_package_evidence.json)
preserves the exact three theorem records, seven used premise records,
and hashes of all three supplied modules, including the definition-only
module. Fresh execution uses `python3 scripts/verify_offcone_completion.py`.
It checks every supplied module hash, strict compilation, declaration
kinds, actual theorem types and axiom sets, premise types, the loaded
project axiom registry, and all pinned dependency revisions. This review
and the two earlier source reviews are included in its input hashes.
The exact checked commit, successful run, preserved report and final
status decision are recorded in [CHECKPOINT.md](../../CHECKPOINT.md).
