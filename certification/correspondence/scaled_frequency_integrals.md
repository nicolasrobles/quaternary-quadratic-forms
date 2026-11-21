# Scaled frequency integrals: equation (5.5)

## Scope and source

This review covers only `aux:Ipiece`: the scaled integral estimate (5.5),
the fixed-frequency regularity assertion immediately before it, and the
common localization and cutoff used there. The source is
`manuscript/quadratic_character_sums_github.tex`, lines 2091–2124, SHA-256
`e3cd28b361ec143d043d4d9ced55939c234648f73f23a05377af4aaefa98b49a`.
No numbered-result status is changed by this review.

The three proof files are copied byte-for-byte from the author's uploaded
`quaternary-quadratic-forms-verified(1).zip`. The package's original six
theorem records and seven used literature-premise records are preserved in
[the extracted evidence](../local/ipiece_package_evidence.json). That file
retains the older manuscript identity and the original aggregate-report hash;
it is not represented as a fresh execution for the current manuscript.

## Endpoints

| Source clause | Lean endpoint |
| --- | --- |
| The scaled estimate (5.5), uniform in the localized weights and parameters | `QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency` |
| A common localization and cutoff, with the scaled estimate for the actual family | `QuaternaryQuadraticForms.source_localized_frequency_integrals` |
| Smooth dependence on the positive scale, with frequency fixed | `QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale` |

The first endpoint is in
[FrequencyIntegralBounds.lean](../../QuaternaryQuadraticForms/FrequencyIntegralBounds.lean),
the second in
[LocalizedFrequencyIntegrals.lean](../../QuaternaryQuadraticForms/LocalizedFrequencyIntegrals.lean),
and the third in
[DeltaIntegralRegularity.lean](../../QuaternaryQuadraticForms/DeltaIntegralRegularity.lean).
All three are needed for the full declared scope: the localization endpoint
alone states differentiability, whereas the separate regularity endpoint
supplies continuous differentiability, in fact smoothness.

## Actual integral, scale and uniformity

The existing `deltaIntegral` is the manuscript's Euclidean integral, with
phase `exp(-2*pi*i*(v dot x)/r)`. The integer lattice is embedded in Euclidean
four-space, and `integerEuclideanNorm` is the source Euclidean norm.

In `ScaledFrequencyIntegralBound`, one positive constant precedes every
localized weight, positive integer modulus `q`, real `B >= 1`, real `t >= 1`,
and nonzero integer frequency `u` with `norm(u) <= sqrt(q)*B^eta`. The derivative
is `deriv (fun s => deltaIntegral F w s v) r`: the frequency `v` is fixed
during differentiation. The bound does not differentiate a composite
frequency depending on `s`.

Set `s = sqrt(q)`, `r = t/(B/s)` and `v = s^(-1) * u`. The proof establishes
`s >= 1`, `s^2 = q`, `r > 0`, and

```text
norm(v) = norm(u)/s > 0,
norm(v) <= B^eta <= B,
r^(-1) = B/(t*s) <= B,
r/norm(v) = t*q/(B*norm(u)).
```

The decay estimate already proved for Lemma 2.2 is applied at epsilon `eta`,
where `0 < eta <= 1/4`. The exact factorization

```text
r^(1-2*eta) * norm(v)^(-1+eta)
  = (r/norm(v)) * (r^(-1))^(2*eta) * norm(v)^eta
```

then yields `C * t*q/(B*norm(u)) * B^(3*eta)`, as in (5.5).
The stronger analytic range `q >= 1`, `B >= 1` includes the manuscript's
range `B >= 9`, `q <= B`; no squarefree or coprimality condition is needed
for this integral estimate. Those arithmetic conditions remain part of the
later frequency-sum problems.

The localization endpoint invokes the existing `source_delta_integrals`
certificate for Lemma 2.2. It produces a single `delta` and `r0`, with
`0 < delta <= 1` and `r0 >= 1`, before the exponent and individual localized
weights. The value and derivative vanish for all `r >= r0`. For localized
pieces meeting the cone, the same family satisfies the scaled estimate.
Thus no new internal conclusion has been introduced as a literature premise.

## Regularity on positive scales

`deltaIntegral_contDiffOn_scale` works for every smooth real function `F`,
every smooth compactly supported complex weight, and every fixed frequency.
The integrand is jointly smooth on the open set `r > 0`, and its spatial
support is contained in a single compact ball independent of `r`.

The parameterized convolution theorem from the pinned mathlib source applies
to that fixed compact support. At the zero convolution argument, the two
negations recover the original weight, kernel and exponential phase exactly.
The conclusion is `ContDiffOn R infinity` on `Ioi 0`. Specializing `F` to the
actual quadratic form gives the source endpoint, including the manuscript's
continuous first derivative. No assertion is made at `r = 0`.

## Supporting exports and literature dependencies

The three files contain six theorem exports. The additional general
regularity theorem supports its quadratic specialization. The uniform
singular-integral bound follows by applying the existing zero-frequency
error estimate at the common cutoff, where the oscillatory integral
vanishes. The small-modulus helper chooses an integer `j > 2/eta` and proves
the corresponding `C/Q^2` estimate. These helpers do not change the status
of Lemma 5.4 or any other numbered result.

The scaled estimate and both numerical helpers use only the usual logical
foundations. The regularity theorems additionally use the already registered
Heath–Brown delta input. The localization theorem uses the seven existing
analytic premises recorded in the extracted evidence: delta construction,
weight localization, singular graph limit, zero-frequency approximation,
integral reduction, oscillatory bounds and the general graph area formula.
There is no new literature declaration or change to an existing premise.

## Review and execution evidence

Independent source-correspondence review found no required fatal, serious,
moderate or light correction in this three-file batch. The six actual theorem
types and axiom sets also passed the focused kernel inspection.

The [focused GitHub run 44848399842](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44848399842)
passed at commit [fef53391ba75](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/fef53391ba75f764ebe891441362ce73c8af6d52).
The three supplied modules built successfully and passed strict compilation;
all six actual theorem types and axiom sets matched the supplied records.
The seven used literature-premise types and all nine pinned dependency
revisions also passed inspection. All 59 recorded proof/checker input hashes
match the integrated files. The [preserved execution report](../ci/ipiece_run_44848399842_attempt_1.json)
records the precise scope and results. Its SHA-256 is
`64224914265624b5775a0fe480792ec7f4ac17776c00ed2d6637b7f66fb61384`.
This focused execution certifies only `aux:Ipiece` and its supporting exports;
the ordinary full-repository workflow remains an additional regression check.

The focused check is reproducible with `python3 scripts/verify_ipiece.py`
after fetching the pinned dependencies and required official mathlib cache.
It runs the existing metadata verifier, checks the dependency revisions,
builds only these three modules and their existing import closure, recompiles
the three supplied files under strict options, inspects declaration kinds,
and compares the six actual types and axiom sets with the supplied records.
The repository's full verification workflow remains an additional regression
check.
