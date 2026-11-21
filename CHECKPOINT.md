# Verification checkpoint: Dual-cone count and modulus partial summation

## Current checkpoint: Dual-cone count and modulus partial summation

This step supplies two prerequisites for Lemma 5.3: the reciprocal Euclidean
norm sum on the dual cone, and Abel partial summation for the inner modulus
sum. The `source_dual_cone_count` endpoint gives the source estimate
$\sum_{0<\|u\|\le U,\ F^*(u)=0}\|u\|^{-1}\ll U^{1+\epsilon}$.
See the [focused source review](certification/correspondence/oncone_prerequisites.md).

The two exact supplied modules total 280 lines and add four supporting theorem
exports with no new literature premise.

| Supplied module | Lines | Supporting exports |
| --- | ---: | ---: |
| `DualConeCounting.lean` | 118 | 1 |
| `ConeFrequencyAbel.lean` | 162 | 3 |

Focused verification passed. **`aux:conecount` is Certified**. **Lemma 5.3 remains Pending**: its final mixed-sum factors,
Poisson normalization, and count assembly still require certification.
No numbered result is promoted in this batch.

The accepted scope is **1,187 theorem exports, 283 proof modules,
and 328 verifier input files**, with the same **12 registered literature
premises** and nine pinned dependency revisions. The numbered inventory stays
**27 Complete, 0 Partial, 0 Active, 15 Pending**; the supplementary coverage is **7 Certified, 26 Pending**.

The [focused GitHub run 44856104093](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44856104093)
passed at proof commit [7e0697d2a908](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/7e0697d2a908b501e2030a1803bc25fd8e42def6).
Both supplied modules built successfully and passed strict compilation;
all four actual theorem types and axiom sets matched the supplied records.
Each export uses only `Classical.choice`, `Quot.sound`, and `propext`.
All nine pinned dependency revisions passed inspection, and all
144 recorded proof/checker/review input hashes match the integrated files,
including the 132-module project import closure.
The [preserved execution report](certification/ci/oncone_prerequisites_run_44856104093_attempt_1.json) records the precise scope
and results. Its SHA-256 is
`405d09a62468385521d8783f8353bee40c34ec27861f14295214e968cdfd367a`.
This execution and the source reviews complete `aux:conecount` and check
the supporting inner-modulus estimates. Lemma 5.3 remains Pending. The
ordinary full-repository workflow remains an additional regression check.

## Historical checkpoint: Lemma 5.2 complete

This step assembles the actual averaged mixed complete sums and restores the
Poisson factor $c_Q B^2/q^3$. The `source_offcone` endpoint returns both source
clauses with the same localization $\delta$ and cutoff $r_0$: for
$U=\sqrt q B^\eta$, frequencies $\|u\|>U$ contribute $O(1)$, and frequencies
$0<\|u\|\le U$ with $F^*(u)\ne0$ contribute $O((Bq)^{1+8\eta})$.
See the [focused source review](certification/correspondence/offcone_completion.md).

The three exact supplied modules total 247 lines and add three theorem exports
with no new literature premise.

| Supplied module | Lines | Theorem exports |
| --- | ---: | ---: |
| `FrequencySourceData.lean` | 26 | 0 (definition) |
| `OffConeModulusAverage.lean` | 123 | 1 |
| `OffConeFrequencyTheorem.lean` | 98 | 2 |

Focused verification passed. **Lemma 5.2 is Complete**.
No other numbered result or supplementary status is promoted.

The accepted scope is **1,183 theorem exports, 281 proof modules,
and 325 verifier input files**, with the same **12 registered literature
premises** and nine pinned dependency revisions. The resulting numbered
inventory is **27 Complete, 0 Partial, 0 Active, 15 Pending**; supplementary
coverage remains **6 Certified, 27 Pending**.

The [focused GitHub run 44854581990](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44854581990)
passed at proof commit [d53d0676bd86](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/d53d0676bd861b79c319f75134ea75ec675f74b8).
All three supplied modules built successfully and passed strict compilation;
the three actual theorem types and axiom sets matched the supplied records.
The seven used literature-premise types and all nine pinned dependency
revisions also passed inspection. All 181 recorded proof/checker/review
input hashes match the integrated files, including the 170-module project
import closure and all three source correspondence reviews.
The [preserved execution report](certification/ci/offcone_completion_run_44854581990_attempt_1.json) records the precise scope
and results. Its SHA-256 is
`64aa693eceda16736944b0bf1a7a5c18511a7626aa21470d865796cb0bea6027`.
This focused execution and the source review establish both clauses of
Lemma 5.2. The ordinary full-repository workflow remains an additional
regression check.

## Historical checkpoint: Lemma 5.2, off-cone reduction

This step covers supporting gcd reduction, dual-form growth bounds, and
average-scale bounds for the bounded off-cone clause of Lemma 5.2. The two
exact supplied modules (221 lines) add six supporting theorem exports and no
literature premise. See the
[focused source review](certification/correspondence/offcone_reduction.md).

| Supplied module | Lines | Supporting exports |
| --- | ---: | ---: |
| `OffConeFrequencyReduction.lean` | 130 | 4 |
| `OffConeFrequencyScales.lean` | 91 | 2 |

Focused verification passed. This is supporting progress only:
**Lemma 5.2 remains Partial**. Its large-frequency $O(1)$ clause is complete;
the bounded off-cone contribution $O((Bq)^{1+8\eta})$ remains **Pending**
until the final averaging and normalization assembly. No numbered clause,
numbered status, or supplementary status is promoted in this batch.

The accepted scope is **1,180 theorem exports, 278 proof modules,
and 322 verifier input files**, with the same **12 registered literature
premises** and nine pinned dependency revisions. The numbered inventory stays
**26 Complete, 1 Partial, 0 Active, 15 Pending**; supplementary coverage stays
**6 Certified, 27 Pending**.

The [focused GitHub run 44852824398](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44852824398)
passed at proof commit [484116fd9065](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/484116fd906503b85fd1f87d3e5e6e43e4ee1263).
Both supplied modules built successfully and passed strict compilation;
all six actual theorem types and axiom sets matched the supplied records.
Each export uses only `Classical.choice`, `Quot.sound`, and `propext`.
All nine pinned dependency revisions passed inspection, and all
176 recorded proof/checker/review input hashes match the integrated files,
including the 167-module project import closure.
The [preserved execution report](certification/ci/offcone_reduction_run_44852824398_attempt_1.json) records the precise scope
and results. Its SHA-256 is
`745f500441246744316c46dfaed03852376304a08fbc7f5894a3c6a38b471ac8`.
This focused execution checks the six supporting reductions; it does not
complete the bounded off-cone clause. The ordinary full-repository workflow
remains an additional regression check.

## Historical checkpoint: Lemma 5.2, large-frequency clause

This step is confined to the first clause of Lemma 5.2: frequencies with
$\|u\|>U$ contribute $O(1)$. Three exact supplied modules (403 lines) add
eight supporting theorem exports and no literature premise. See the
[focused source review](certification/correspondence/large_frequency_truncation.md).

Focused verification passed. Lemma 5.2 is **Partial**:
its large-frequency clause is complete, while the bounded off-cone clause
$0<\|u\|\le U$, $F^*(u)\ne0$, with contribution $O((Bq)^{1+8\eta})$,
remains **Pending**. No other numbered result is promoted.

The accepted scope is **1,174 theorem exports, 276 proof modules,
and 320 verifier input files**, with the same **12 registered literature
premises** and nine pinned dependency revisions. The resulting numbered
inventory is **26 Complete, 1 Partial, 0 Active, 15 Pending**; supplementary
coverage remains **6 Certified, 27 Pending**.

The [focused GitHub run 44850308809](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44850308809)
passed at proof commit [bc62790b3f58](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/bc62790b3f582b149d3fd8ab9a21f26d56f8f33c).
The three supplied modules built successfully and passed strict compilation;
all eight actual theorem types and axiom sets matched the supplied records.
The seven used literature-premise types and all nine pinned dependency
revisions also passed inspection. All 141 recorded proof/checker input hashes
match the integrated files, including the 134-module project import closure.
The [preserved execution report](certification/ci/large_frequency_run_44850308809_attempt_1.json) records the precise scope and
results. Its SHA-256 is
`1dea571ecdd1dc04476a17ab35d6aad0243e9ec076327b833dd5d7ffe0e57c1d`.
This focused execution covers only the first clause of Lemma 5.2 and its
supporting exports; the ordinary full-repository workflow remains an
additional regression check.

The manuscript, PDF, and source fingerprints are unchanged. Earlier execution
records retain their original scope. The shared arithmetic module also contains
zero-frequency helpers; this checkpoint covers only the large-frequency clause.

## Earlier auxiliary checkpoint: equation (5.5)

That step was confined to `aux:Ipiece`: the scaled-integral estimate, smoothness
in the positive scale with frequency fixed, and the common localization and
cutoff used immediately before Lemma 5.2. The three supplied modules add six
supporting theorem exports and no literature premise. See the
[focused source review](certification/correspondence/scaled_frequency_integrals.md).

The integrated scope then contained **1,166 theorem exports, 273 proof modules, and
316 verifier input files**, with the same **12 registered literature premises**
and nine pinned dependency revisions. The numbered status was
**26 Complete, 0 Partial, 0 Active, 16 Pending**. This auxiliary obligation became **Certified**, bringing supplementary
coverage to **6 Certified, 27 Pending**. Lemma 5.2 remained Pending at that checkpoint.

Checked proof commit: [fef53391ba75](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/fef53391ba75f764ebe891441362ce73c8af6d52)
on `verify/ipiece-2026-11-20`.

The [focused GitHub run 44848399842](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44848399842)
passed at commit [fef53391ba75](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/fef53391ba75f764ebe891441362ce73c8af6d52).
The three supplied modules built successfully and passed strict compilation;
all six actual theorem types and axiom sets matched the supplied records.
The seven used literature-premise types and all nine pinned dependency
revisions also passed inspection. All 59 recorded proof/checker input hashes
match the integrated files. The [preserved execution report](certification/ci/ipiece_run_44848399842_attempt_1.json)
records the precise scope and results. Its SHA-256 is
`64224914265624b5775a0fe480792ec7f4ac17776c00ed2d6637b7f66fb61384`.
This focused execution certifies only `aux:Ipiece` and its supporting exports;
the ordinary full-repository workflow remains an additional regression check.

The manuscript, PDF, source fingerprints, and earlier certificates are
unchanged. The editorial-revision and Lemma 5.1 records below retain their
historical scope and execution evidence.

## Current editorial revision of 20 November 2026

The second uploaded TeX and PDF replace the preceding manuscript snapshot. All
42 numbered statements and all 199 displayed formulas are byte-identical. Of
the 40 proof blocks, 29 are byte-identical; eleven contain punctuation or prose
edits, with unchanged mathematical expressions and proof arguments. All source
line locators, result numbers and PDF label pages remain unchanged. The PDF
still has 35 pages.

The [comparison record](certification/manuscript_revisions/2026-11-20-editorial-2.json)
records the exact uploaded file identities and the changed proof prose. The
source fingerprints have been refreshed without changing the verification
rules. Metadata verification passed. All 273 tracked Lean files, dependency
pins, literature premises, theorem exports and certification statuses are
unchanged: **26 Complete, 0 Partial, 0 Active, 16 Pending**. This editorial
update adds no certified result. The push triggers a fresh full GitHub Actions
run; the completed run documented below belongs to the preceding revision.

## Earlier manuscript revision of 20 November 2026

The author's updated TeX and PDF replace the preceding snapshot. All 42 numbered
statements, all 40 proof blocks, and the displayed equations are byte-identical.
The changes concern exposition in the introduction, Section 2.1 and conclusion,
and the acknowledgement. The source identities, PDF page references and four
supplementary source links have been updated. All Lean files, dependency pins,
registered premises, theorem exports and certification statuses are unchanged.
The numbered status remains **26 Complete, 0 Partial, 0 Active, 16 Pending**.

The [revision comparison](certification/manuscript_revisions/2026-11-20.json)
records the old and new file identities and the unchanged statement hashes.
Historical verification reports and source reviews retain the exact manuscript
identity they originally checked. The mathematical checkpoint below remains
Lemma 5.1; the manuscript revision does not add a certified result.

### Verification of the earlier manuscript revision

The full GitHub verifier passed on the exact manuscript-update commit
[53df45a82252](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/53df45a82252855d6063c153bb7abd54edecd61d).
[Run 44816756668, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44816756668)
completed successfully on 20 November 2026; the verification job finished at
21:31:55 UTC. The build completed successfully with 3,509 jobs.

The new report preserves **all 1,160 complete theorem records, all 12 registered
premise records, all nine pinned dependency revisions, and the certification
status** from the preceding full run. All **312 inspected input hashes** match
the checked commit. The only changed inspected inputs are the source identity
record, dependency inventory, and verifier's manuscript SHA-256 constant.
All 273 tracked Lean files remain byte-identical to the preceding checkpoint.

- [Report comparison](certification/manuscript_revisions/2026-11-20_ci.json).
- [Fresh full CI report](certification/ci/run_44816756668_attempt_1.json).
- [Original CI artifact ZIP](certification/ci/run_44816756668_attempt_1.zip), whose SHA-256 matches GitHub's artifact digest.

The local revision check was metadata-only. The full Lean execution above ran
in GitHub Actions. Older local reports, CI archives and source reviews retain
their original manuscript identities. This evidence archive changes documentation
and adds the new reports; all inputs inspected by the successful run remain
identical to the checked manuscript-update commit.

## Historical Lemma 5.1 status

Complete: **26**. Partial: **0**. Active numbered targets: **0**.
Pending: **16**. Supplementary groups: **5 Certified, 28 Pending**.

### Complete Lemma 5.1

**Lemma 5.1 is Certified relative to the registered delta and Poisson inputs.**
For the original supplied functions and a smooth compactly supported weight,
with `Q=B/sqrt(q)>=3`, the exact identity is

$$
T_q(B;w)=c_Q\frac{B^2}{q^3}\sum_{c\ge1}\frac1{c^4}
 \sum_{u\in\mathbb Z^4}\mathcal S_{q,c}(u)
 I^*_{c/Q}\!\left(\frac{u}{\sqrt q};w\right).
$$

The lattice sum has finite support, only finitely many positive moduli
contribute, and every frequency series converges absolutely. The endpoint
[source_delta_poisson](QuaternaryQuadraticForms/PoissonTheorem.lean) retains
the actual source weights, complete sums, fixed kernel, and Euclidean integral.
See the [source review](certification/correspondence/delta_poisson.md).

The general affine Poisson formula is newly registered in the
[Poisson input review](certification/correspondence/poisson_summation.md).
Lemma 2.1 already supplies the certified delta identity. Residue reindexing,
phase signs, denominator cancellation, the `B^4` Jacobian, and the final
`B^2/q^3` normalization are internal deductions. No pending proof obligation
is assumed as a prerequisite for this lemma.

This milestone adds **45 theorem exports in 14 modules**, bringing the
registered totals to **1,160 exports, 270 modules, 312 inspected inputs,
and 12 literature premises**, with 21 mapped source groups and nine pinned
dependency revisions. The frozen manuscript is unchanged. **Proposition 5.1
remains Pending**; its remaining analytic obligations are separate from
this lemma. This session stops after Lemma 5.1.

### Historical Lemma 5.1 verification

<!-- BEGIN LEMMA_5_1_VERIFICATION -->

**The complete local aggregate verifier and independent GitHub verification
both passed for the exact Lemma 5.1 proof tree.** They check the frozen source,
all project modules under strict options, declaration kinds, complete types,
axiom dependencies, status accounting, and pinned dependency revisions.

- Checked proof commit: [345e447a64bd](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/345e447a64bd10aa2b8cad7250e8c15fdad663b9).
- Proof tree: `afe67eef39c75552a164b84f3644025c0205814d`.
- [GitHub run 43780394948, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43780394948), completed successfully at 2026-11-16T00:48:54Z.
- Verification job: `133016026454`; artifact: `14189195565`.
- Artifact name: `lean-verification-345e447a64bd10aa2b8cad7250e8c15fdad663b9-1`.
- Local build: `Build completed successfully (3509 jobs).`.
- CI build: `Build completed successfully (3509 jobs).`.

| Preserved evidence | Bytes | SHA-256 |
| --- | ---: | --- |
| [Local report](certification/verification_report.json) | 1,758,056 | `df12c93de4f90f09b5fe7b1d7adfe31be8f53774cbc9eb69a895d6d450d32f35` |
| [CI report](certification/ci/run_43780394948_attempt_1.json) | 1,778,385 | `597786643cd305b0b158b0014208b662b766f8ecd26c94b0907357755f62e783` |
| [Original CI artifact ZIP](certification/ci/run_43780394948_attempt_1.zip) | 208,270 | `786a87b2d64c217548cb440992bfce3e27f8219123a3839c07959e883ab0ebfe` |

The reports agree on **all 18 verification-content fields**, including
**1,160 complete theorem records, 270 project modules, 312 inspected input
hashes, 12 registered literature premises, 21 mapped source groups, and nine
pinned dependency revisions**. Every inspected input and export source hash
matches the exact proof commit. Only the generation timestamp and build log
may differ; report initialization timestamps are not completion times. The
original ZIP digest matches GitHub's digest.

All **1,115 prior theorem records and all 11 prior premise records are
unchanged**. The 45 new theorem types and axiom sets match their separate
strict inspection. Beyond the standard logical foundations, **33 use no
literature premise, eight use only the existing Heath–Brown delta input,
one uses only general four-dimensional Poisson summation, and three use both**.
The newly registered general Poisson premise has strict type SHA-256
`40a16daa09a156fd73fe1f6bf8b7599210b25c0dd061b9746a4bd802d1402d88`; see its
[input review](certification/correspondence/poisson_summation.md).

The [source correspondence](certification/correspondence/delta_poisson.md)
records the exact formula with the original supplied weights, finite lattice
and positive-modulus support, and absolute convergence of every frequency
series. Residue reindexing, phase signs, the `B^4` Jacobian, and the final
`B^2/q^3` normalization are internal deductions. The required Lemma 2.1 is
already complete; no pending manuscript obligation is assumed here.

This evidence archive changes only the current verification blocks in README
and CHECKPOINT, the local report, and the preserved CI report and original ZIP.
All historical evidence blocks remain unchanged. The frozen manuscript, PDF,
Lean proofs, verifier, inventory, and inspected metadata remain those of the
checked proof commit. The numbered status is **26 Complete, 0 Partial,
0 Active, 16 Pending**; supplementary status remains **5 Certified, 28 Pending**.
The whole paper is not certified. Work stops after Lemma 5.1; Proposition 5.1,
`aux:Ipiece`, `aux:conecount`, and the general cone-vertex singular-integral
obligation remain Pending.

<!-- END LEMMA_5_1_VERIFICATION -->

### Earlier complete Lemma 2.3

**Lemma 2.3 is Certified in full, with no literature premise.**
For every nonsingular symmetric rational `4 x 4` matrix with nonsquare
rational determinant and every `epsilon>0`, one positive constant is chosen
before all real `U>=1`, bounding the actual number of integer zeros in the
Euclidean ball by `C*U^(2+epsilon)`. The proof includes the rationally
anisotropic case, the exact hyperbolic normal form and discriminant identity,
an injective integral change of variables, both signs of divisors, and the
zero binary-coordinate slice. The endpoint also proves finiteness of the
literal source set.
See [source_quadric_count](QuaternaryQuadraticForms/QuadricCountingTheorem.lean)
and the [source correspondence review](certification/correspondence/quadric_count.md).

This milestone adds **28 theorem exports in nine modules**, bringing the
registered total to **1,115 exports in 256 modules**, with **296 inspected
inputs** and the same **11 registered literature premises**. All 28 new
exports use only the standard logical foundations. The frozen manuscript
is unchanged. The separate weighted consequence **aux:conecount remains
Pending**. Work stops after Lemma 2.3 for this session.

### Earlier Lemma 2.3 verification

<!-- BEGIN LEMMA_2_3_VERIFICATION -->

**The complete local aggregate verifier and independent GitHub verification
both passed for the exact Lemma 2.3 proof tree.** They check the frozen source,
all project modules under strict options, declaration kinds, complete types,
axiom dependencies, status accounting, and pinned dependency revisions.

- Checked proof commit: [ae42d40d67d1](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/ae42d40d67d1b27bc8cd8d16547ff7719786ea50).
- Proof tree: `bad4a56956eca148afec8e08af8519503b7c2cc9`.
- [GitHub run 43773643293, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43773643293), completed successfully at 2026-11-15T23:36:01Z.
- Verification job: `132994865473`; artifact: `14186516176`.
- Local build: `Build completed successfully (3495 jobs).`.
- CI build: `Build completed successfully (3495 jobs).`.

| Preserved evidence | Bytes | SHA-256 |
| --- | ---: | --- |
| [Local report](certification/verification_report.json) | 1,682,646 | `1cdf5856d7900ccfe63b5e850b5516484039f2205016af0fbda96a756a6658d8` |
| [CI report](certification/ci/run_43773643293_attempt_1.json) | 1,701,939 | `c0749173104d750e1003feecdfff7de9c251de5e4c82ee0838846c6247bb883e` |
| [Original CI artifact ZIP](certification/ci/run_43773643293_attempt_1.zip) | 198,838 | `37c311009867d07e0832d93396a11efabba9b1bda830acc3e9367bf51662a1a9` |

The reports agree on **all 18 verification-content fields**, including
**1,115 complete theorem records, 296 inspected input hashes, 11 registered
literature premises, and nine pinned dependency revisions**. Every inspected
input and export source hash matches the exact proof commit. Only the
generation timestamp and build log differ; report initialization timestamps
are not completion times. The original ZIP digest matches GitHub's digest.

All **1,087 prior theorem records and all 11 prior premise records are
unchanged**. The 28 new theorem types and axiom sets match their separate
strict inspection; each uses only `propext`, `Classical.choice`, and
`Quot.sound`. Independent source correspondence found no gap or mismatch.
No new literature premise is added or used by Lemma 2.3.

The evidence archive changes only documentation and its inventory generator,
the local report, and the preserved CI report and ZIP. The frozen manuscript, PDF, Lean proofs,
verifier, and inspected metadata remain those of the checked proof commit.
The numbered status is **25 Complete, 0 Partial, 0 Active, 17 Pending**;
supplementary status remains **5 Certified, 28 Pending**. The whole paper
is not certified. Work stops here; `aux:conecount` remains Pending.

<!-- END LEMMA_2_3_VERIFICATION -->

### Earlier complete Lemma 2.2 and actual surface normalization

**Lemma 2.2 is Certified relative to its registered literature inputs.**
For a fixed symmetric nonsingular form and a smooth complex weight family
with common annular support and coordinate derivative bounds, the actual
delta integral uses the same fixed Heath–Brown kernel as Lemma 2.1 and the
actual localized weights. One positive localization scale and one cutoff
are selected before every weight and center. Above the cutoff,
both the integral and its derivative with frequency held fixed vanish for
every piece. For the pieces whose closed support meets the zero set, all
positive scales satisfy the zero-frequency approximation, derivative bound,
rapid nonzero-frequency decay, and combined epsilon estimate, with constants
uniform over the family. The singular integral is the actual normalized
Euclidean surface integral, and its absolute integrability is proved for
these pieces. The complete source endpoint is
[source_delta_integrals](QuaternaryQuadraticForms/DeltaIntegralTheorem.lean).

The separate **aux:weight_pieces is also Certified**, using no literature
premise: the fixed normalized four-dimensional bump has unit integral, the
pieces reconstruct the original weight, their supports lie in the original
support and within Euclidean distance `2*delta` of the center, and their
derivatives have common bounds.
Five precise Heath–Brown analytic inputs and Simon's general graph area
formula are newly registered. The quadratic chart, its Jacobian and gradient
ratio, surface normalization, coordinate transport, finite choice of common
constants, and extension to all positive scales are internal deductions.
See the [complete source review](certification/correspondence/delta_integrals.md)
and the [surface-measure review](certification/correspondence/surface_area_formula.md).

**The requested coefficient identity and bound, aux:Sxi and aux:Sxibound,
are also proved.** For a fixed symmetric nonsingular integral form with
nonsquare determinant, positive squarefree `q` coprime to the source excluded
modulus, and the original supplied local functions, the actual coefficient
satisfies

$$
\mathfrak S_\xi(q)
=\frac{C_q(0)}{q^3}
 \lim_{X\to\infty}\sum_{\substack{1\le c\le X\\(c,q)=1}}
 \frac{S_c(0)}{c^4}
=\mathfrak S_F\prod_{p\mid q}\frac{C_p(0)}{p^3\sigma_p}.
$$

Under the original local Fourier bound with `K>=1`, the explicit estimate is

$$
|\mathfrak S_\xi(q)|
\le |\mathfrak S_F|\frac{(4K)^{\omega(q)}}q
\le C_{F,K,\varepsilon}q^{-1+\varepsilon}.
$$

For every `epsilon>0`, the positive constant is chosen before the character
level `M`, character `chi`, excluded modulus `N`, local functions `xi`,
polynomials `D`, and `q`. The proof retains the actual increasing-modulus
series, proves the prime-index bridge, and covers `q=1` and `S_F=0`.
Only good-prime densities are inverted; no division by the global coefficient
or a Fourier value is used. The fourteen new exports in three modules use no
literature premise. See the
[identity](QuaternaryQuadraticForms/SourceMainCoefficient.lean),
[uniform bound](QuaternaryQuadraticForms/SourceMainCoefficientBound.lean),
and [source correspondence](certification/correspondence/main_coefficient.md).

### Earlier Lemma 2.2 and main coefficient verification

<!-- BEGIN LEMMA_2_2_VERIFICATION -->

This combined milestone adds **169 public theorem exports in 27 modules**:
155 exports for Lemma 2.2 and weight localization, followed by fourteen for
the requested coefficient identity and bound. The registered scope becomes
**1,087 theorem exports, 247 project Lean modules, and 286 inspected inputs**.
The new scope includes the fixed kernel, actual complex weight pieces,
shared localization constants, fixed-frequency differentiation, all four
integral estimates at all positive scales, and the normalized Euclidean
surface integral and its integrability. It also includes the actual
ordered-series coefficient, exact prime product, explicit finite-prime
bound, and uniform epsilon estimate.

**The complete local aggregate verifier passed**, including the full
build, strict rechecking of every project module, and actual declaration
kind, complete type, and axiom inspection of all registered exports.

- Checked proof commit: [a655331d5496](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/a655331d549669ffcc55c1a52bffee0ba623d62e).
- Proof tree: `1b61ab12b17e0b7977c58fffb66c1a5f3565e3b2`.
- [Preserved local report](certification/verification_report.json), 1,645,188 bytes.
- Local report SHA-256: `66749d911cba345a4604abbe5604894accaaa314f8b99a46a377f0dbdf817d35`.
- Local build: `Build completed successfully (3486 jobs).`.

**Independent GitHub verification passed for the exact published proof
commit.** [Run 43768884969, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43768884969)
completed successfully at 2026-11-15T22:46:18Z; every job step succeeded.
The reports' initialization timestamps precede execution and are not
completion times. The interrupted earlier local invocation left an empty
file; the preserved local report is from the successful continuation run.

- Verification job: `132980085858`; artifact: `14184307877`.
- CI build: `Build completed successfully (3486 jobs).`.
- [Preserved CI report](certification/ci/run_43768884969_attempt_1.json), 1,663,820 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43768884969_attempt_1.zip), 192,872 bytes.
- CI report SHA-256: `61a193b28a292046ea737ee0fad1226fb06d0d106e3ba0627010f0fa6bf541eb`.
- ZIP SHA-256: `80ab1d142836d7caa30e9c29af41002e2c3fdcd192daf0cdf51d7b181d85e288`.

The original ZIP digest agrees with GitHub's recorded digest. The local
and CI reports agree on **all 18 verification-content fields**, including
1,087 complete theorem records and 286 input hashes. Every inspected input
and export source hash matches the exact published proof tree. The only
execution-specific differences are the generation timestamp and build log.

All **918 earlier complete theorem records**, the five earlier literature
premise records, and nine dependency revisions are exactly preserved.
All 169 new complete types and axiom profiles match the recovered separate
strict inspection; the six new premise type hashes match their registered
types. Independent source-correspondence reviews of Lemma 2.2 and both
coefficient obligations passed. The evidence archive changes only README,
CHECKPOINT.md, the local report, and the exact CI report and artifact.
The frozen manuscript, PDF, proof files, verifier, and inspected metadata
remain those of the checked proof commit.

There are **11 separately registered literature premises across 21 mapped
source groups**. The five earlier premises are retained. The six new inputs
are Heath–Brown's uniform localization, thin-slab graph limit,
zero-frequency approximation, fixed-frequency integral reduction, and
auxiliary oscillatory estimates, together with Simon's general graph area
formula. Each premise has its own recorded type and source locator; these
premises are counted separately from the proved exports. The coefficient
identity and bound add and use no literature premise.

The actual bump normalization and weight reconstruction, family derivative
bounds, quadratic gradient and Hessian calculations, positive-root chart,
area-to-gradient ratio, actual surface transport, finite family of common
constants, and cutoff extension are proved internally. The normalized
surface measure uses the three-dimensional unit-ball volume divided by
`2^3`, accounting for mathlib's raw diameter-cubed Hausdorff convention.
The general area formula is the separately disclosed geometric input;
Heath–Brown's thin-slab statement is not silently identified with a surface
integral.

The coefficient proof preserves the increasing-modulus series and original
local functions. It proves
`S_xi(q)=S_F*prod_(p|q) C_p(0)/(p^3*sigma_p)` and
`|S_xi(q)|<=|S_F|*(4K)^omega(q)/q<=C_(F,K,epsilon)*q^(-1+epsilon)`.
The positive constant precedes `M, chi, N, xi, D, q`. The modulus-one
identity and character independence of `S_F` are explicit; zero global
coefficients are retained multiplicatively, and only good-prime densities
are inverted.

The combined ledger scope has **24 Complete, 0 Partial, 0 Active, 18 Pending**
numbered results and **5 Certified, 28 Pending** supplementary groups.
This milestone completes `lem:integrals`, `aux:weight_pieces`, `aux:Sxi`,
and `aux:Sxibound`. The requested Lemma 2.2 work and return to both
coefficient obligations are complete relative to the registered literature
inputs, with matching successful local and GitHub verification of the exact
proof commit. The general cone-vertex integrability obligation, remaining
analytic assembly, global proposition,
and main theorems remain Pending. No further proof target is started or
automatically selected by this checkpoint. Earlier execution evidence below
retains its historical scope.

<!-- END LEMMA_2_2_VERIFICATION -->

### Earlier session boundary after Lemma 2.3

The requested Lemma 2.3 is the last proof target of this session. The separate
weighted dual-cone estimate `aux:conecount` remains Pending for future work.
No further target is automatically selected or started.

### Earlier complete Lemma 2.1 and uniform normalization

**Lemma 2.1 is Certified relative to the registered Heath–Brown input.**
The one fixed, explicitly defined source kernel is smooth on the positive
half-plane and has the source size and support bounds. The actual coefficient
`c(Q)=Q/S(Q)` is positive for every real `Q>=3`, and the exact delta identity
holds for every integer frequency, including zero and negative frequencies.
For every real `j>=1`, one positive constant is chosen before all `Q>=3`
in `|c(Q)-1| <= C_j Q^(-j)`. The outer sum is proved finite, with cutoff
`c<=floor(max(Q,2*|n|/Q))`, and retains the original residue-unit phases.
The complete endpoint is
[source_delta_symbol](QuaternaryQuadraticForms/DeltaSymbolTheorem.lean).
Its registered literature premise records the exact source construction;
uniform positive normalization, the rapid normalized error, division in
the identity, phase agreement, and finite support are internal deductions.
See the [complete source review](certification/correspondence/delta_symbol.md).

### Earlier Lemma 2.1 verification

<!-- BEGIN LEMMA_2_1_VERIFICATION -->

This milestone adds **29 public theorem exports in five modules**, bringing
the verified scope to **918 theorem exports, 220 project Lean modules,
and 256 inspected inputs**. The complete source endpoint and independent
source review cover the fixed common kernel, C-infinity smoothness,
positive normalization at every real Q>=3, every real decay order j>=1,
all integer frequencies, modulus one, actual residue phases, and finite
outer support.

**The complete local aggregate verifier passed**, including the full
build, strict rechecking of every project module, and actual declaration
kind, complete type, and axiom inspection of all registered exports.

- Checked proof commit: [5f6eee91f968](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/5f6eee91f968a2fe855d2b18b7820ba4511c9245).
- Proof tree: `c0c92a68668b04eda13c05d2e0506df1a65b99c5`.
- [Preserved local report](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/ae84e9ff0539e0451121ea630781920cd21ac684/certification/verification_report.json), 1,362,455 bytes.
- Local report SHA-256: `f812afe8927558a565228abfb35002330e1fd30393c035e2d8921e949e57532e`.
- Local build: `Build completed successfully (3445 jobs).`.

**Independent GitHub verification passed for the exact published proof
commit.** [Run 43762915504, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43762915504)
completed successfully at 2026-11-15T21:35:44Z; every job step succeeded.
The reports' initialization timestamps precede execution and are not
completion times.

- Verification job: `132961498175`; artifact: `14182205232`.
- CI build: `Build completed successfully (3445 jobs).`.
- [Preserved CI report](certification/ci/run_43762915504_attempt_1.json), 1,378,890 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43762915504_attempt_1.zip), 161,671 bytes.
- CI report SHA-256: `f33b9e9b9eb87d5b0f977c5e103d9a9cbb9428d4aaa9a935299b41d1959e9c64`.
- ZIP SHA-256: `3dbb38321b23aa2cf287392389cb81c07d93c3466492cdcb6ea6ce2d21e42f13`.

The original ZIP digest agrees with GitHub's recorded digest. The local
and CI reports agree on **all 18 verification-content fields**, including
918 complete theorem records and 256 input hashes. Every inspected input
and export source hash matches the exact published proof tree. The only
execution-specific differences are the generation timestamp and build log.

All **889 earlier complete theorem records**, the four earlier literature
premise records, and nine dependency revisions are exactly preserved.
All 29 new complete types and axiom profiles match the separate strict
inspection. Twenty generic normalization/support exports use exactly
Classical.choice, Quot.sound, and propext. Nine source-specific exports
add only the newly registered `Trusted.heathBrown_delta_data` input;
its actual kind and complete type are inspected separately. There are
five registered literature premises and 20 mapped source groups.

The new input concerns the actual cited construction: its bump and kernel
properties, unnormalized identity, and raw sampling error. The manuscript's
uniform positive denominator bound, normalized rapid error, division in
the delta identity, phase agreement, and finite support are internal
deductions. In particular the proof divides by S(Q) only after proving
positivity throughout Q>=3; no normalized formula at Q=2 is imported.

At that milestone, the frozen manuscript and PDF, all earlier 215 project
modules, and the pinned verifier remained unchanged. The ledger then had
**23 Complete, 0 Partial, 0 Active, 19 Pending** numbered results, with
**2 Certified and 31 Pending** supplementary groups. Only lem:delta was
promoted by that milestone; whole-paper certification remained false.
Its announced next numbered targets were Lemmas 2.2 and 2.3. This evidence
retains its historical scope; the current continuation status is recorded below.

<!-- END LEMMA_2_1_VERIFICATION -->

### Earlier complete Lemma 3.11 and the exact factorization

**Lemma 3.11 is Certified in full.** For the literal positive squarefree
factorization q=q1*q2 with (q,N)=1, the actual source Fourier sums satisfy
`sum_(0<||u||<=U, q1|F*(u)) |C_q2(u)|/||u|| <= C q^epsilon q2^(3/2) (U^3/q1 + q2^(1/2) U^2)`.
The positive constant depends only on the real degree bound E, the local
bound K, and epsilon, before the matrix, source modulus, original local
functions and polynomials, factorization, and real radius U>=1.
The complete endpoint is
[source_average_frequency_bound](QuaternaryQuadraticForms/SourceAverageFrequencyTheorem.lean).
The exact prime-product identity for C_q and coprime multiplicativity of
S_c also complete the separate aux:Cfactor obligation. No literature
premise is added or used. See the
[complete source review](certification/correspondence/average_frequency.md).

### Earlier Lemma 3.11 verification

<!-- BEGIN LEMMA_3_11_VERIFICATION -->

This milestone adds **14 public theorem exports in six modules**, bringing
the verified scope to **889 theorem exports, 215 project Lean modules,
and 250 inspected inputs**. The complete source endpoint and independent
source review cover the original Fourier sums, the actual adjugate form
and Euclidean norm, the source-only prime families, real degree bounds
and radii, and all modulus-one cases. The constant is chosen before all
matrix, coefficient, weight, modulus, and radius data. Three epsilon/3
factors give exactly q^epsilon, without an additional U^epsilon factor
or logarithm.

**The complete local aggregate verifier passed**, including the full
build, strict rechecking of every project module, and actual declaration
kind, complete type, and axiom inspection of all registered exports.

- Checked proof commit: [0bcf01359690](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/0bcf0135969035a759d7ea9a56e79fb362179101).
- Proof tree: `8136404ff6777f6555f29f1f2c905c9b31e63492`.
- [Preserved local report](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/84b92dce0609ec93cea109b44739f01fcca8a86d/certification/verification_report.json), 1,320,495 bytes.
- Local report SHA-256: `12857f5c9f2ad46dbc7b0b66923343ae3620a81895d1c311105b1bcbffb2f292`.
- Local build: `Build completed successfully (3439 jobs).`.

**Independent GitHub verification passed for the exact published proof
commit.** [Run 43755523278, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43755523278)
completed successfully at 2026-11-15T20:16:36Z; every job step
succeeded. The report initialization timestamp precedes execution and
is not the completion time.

- Verification job: `132938665061`; artifact: `14179001450`.
- CI build: `Build completed successfully (3439 jobs).`.
- [Preserved CI report](certification/ci/run_43755523278_attempt_1.json), 1,336,550 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43755523278_attempt_1.zip), 156,076 bytes.
- CI report SHA-256: `756151c4994cb8c66cfa346f6b5469e9d3fda2128cb2f0525ca7fb12ad5684c3`.
- ZIP SHA-256: `09a16bfaf440b30e9321cb60f33261e460e3f1e95c5338a0e730b22861e6bae7`.

The original ZIP digest agrees with GitHub's recorded digest. The local
and CI reports agree on **all 18 verification-content fields**, including
889 complete theorem records and 250 input hashes. Every inspected input
and export source hash matches the exact published proof tree. The only
execution-specific differences are the generation timestamp and build log.

All **875 earlier complete theorem records**, the four literature-premise
records, and nine dependency revisions are exactly preserved. All fourteen
new complete types and axiom profiles match the separate strict export
inspection. Each new export uses exactly Classical.choice, Quot.sound,
and propext; no literature premise is added or used. The frozen manuscript,
PDF, earlier 209 project modules, and pinned verifier remain unchanged.

The live ledger has **22 Complete, 0 Partial, 0 Active, 20 Pending**
numbered results. Two supplementary groups are Certified and 31 remain
Pending. This milestone completes lem:average and aux:Cfactor; whole-paper
certification remains false. Earlier evidence retains its historical scope.

<!-- END LEMMA_3_11_VERIFICATION -->

### Earlier complete Lemma 3.10 and its epsilon prerequisite

**Lemma 3.10 is Certified in full.** For coprime positive squarefree
q1,h with (q1*h,N)=1, both the actual Euclidean congruence count and
the original inverse-norm weighted sum satisfy the manuscript bounds.
One constant depending only on the real degree bound E>=1 and
epsilon>0 is chosen before the matrix, source modulus, independently
supplied prime polynomials, moduli, and real radius U>=1.
The full source endpoint is
[source_congruence_box](QuaternaryQuadraticForms/SourceCongruenceBoxTheorem.lean).
The prerequisite aux:polynomialbox_epsilon is also Certified, with
coefficient and interval uniformity preserved. No literature premise
is added or used. See the
[complete source review](certification/correspondence/congruence_box.md).

### Earlier Lemma 3.10 verification

<!-- BEGIN LEMMA_3_10_VERIFICATION -->

This milestone adds **37 public theorem exports in ten modules**, bringing
the checked scope to **875 theorem exports, 209 project Lean modules,
and 243 inspected inputs**. All 37 new exports have complete actual
types and axiom profiles using exactly Classical.choice, Quot.sound,
and propext; no literature premise is used. Source correspondence covers
both Euclidean inequalities, the original polynomial domain, real degree
bounds and radii, all modulus-one cases, and full coefficient uniformity.

**Independent GitHub aggregate verification passed at the exact proof
commit [44f50a736906](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/44f50a736906c4d5e12e1fb046cf010c0ad5497a).**
[Run 43753519056, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43753519056)
completed successfully at 19:55:14 UTC on 15 November 2026. Every job
step succeeded, including the full build, strict rechecking of all 209
project modules, and inspection of all actual theorem types and axioms.

- Proof tree: `f0d23fc1051c697d08d79b3bbd339419a0c598fb`.
- Verification job: `132932493681`; artifact: `14177304773`.
- Build: `Build completed successfully (3433 jobs).`.
- [Preserved CI report](certification/ci/run_43753519056_attempt_1.json), 1,300,335 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43753519056_attempt_1.zip), 151,747 bytes.
- ZIP SHA-256: `7804efb9993047f46ea6ae988fe6c1a611098b137dffaaab6425bdf69dba09ac`.
- CI report SHA-256: `e8ce0cec380ef779edd06cc504e0c548ea77a0e30f99dbba147a505a38e476c5`.

The original ZIP digest matches GitHub's recorded digest. All 243 input
hashes and all 875 export source hashes match the immutable proof tree.
All 838 earlier complete theorem records, four literature-premise records,
and nine dependency revisions are exactly preserved. At that checkpoint,
the inventory was 21 Complete, 0 Partial, 0 Active, 21 Pending numbered
results, with one Certified and 32 Pending supplementary groups.
Whole-paper certification remained false.

**A fresh local execution of the complete verifier also passed on the
exact Lemma 3.10 proof commit.** Its [preserved local report](certification/local/lemma_3_10_44f50a7.json)
has 1,300,262 bytes and SHA-256
`f4c17818b7d23b9df83ae378623de3a5661e6de854ef08a3e753e429ec7c67f7`.
The local build ended with `Build completed successfully (3433 jobs).`.
The local and CI reports agree on all 18 verification-content fields,
including all 875 complete theorem records, 243 input hashes, four
unchanged literature-premise records, and nine dependency revisions.
Only the initialization timestamp and build log differ. The report's
initialization timestamp is not the completion time.

<!-- END LEMMA_3_10_VERIFICATION -->

### Earlier complete Lemma 2.4

**Lemma 2.4 is Certified.** The literal simultaneous polynomial-congruence
count in arbitrary real intervals satisfies the exact bound
`(E+...+E^n)^omega(m)*(Y^n/m+Y^(n-1))` for every positive squarefree `m`.
The polynomials are supplied independently at each prime divisor and have
total degree at most `E`. The proof includes modulus one, empty intervals,
constant polynomials, and every degenerate fibre. Its exact constant is
independent of coefficients, interval endpoints, the modulus, and `Y`.
No literature premise is added or used. The full source endpoint is
[`source_polynomial_box`](QuaternaryQuadraticForms/PolynomialBoxTheorem.lean),
with a [complete correspondence review](certification/correspondence/polynomial_box.md).

### Earlier Lemma 2.4 verification

<!-- BEGIN LEMMA_2_4_VERIFICATION -->

The complete Lemma 2.4 milestone adds **49 public theorem exports in
nine modules**, bringing the aggregate scope to **838 theorem exports,
199 project Lean modules, and 232 inspected inputs**. The final source
target compiled successfully with 1,450 jobs under the pinned official
Lean 4.24.0 and mathlib revision.

All 49 declaration kinds, complete actual theorem types, and axiom
dependencies have passed strict inspection and independent review.
Of these, 46 use exactly `Classical.choice`, `Quot.sound`, and `propext`;
the dimension-one constant identity uses only `propext`, and the two
definitional recurrence identities use no axioms. No new export uses
any registered literature premise.

Independent source review covers the exact constant, coefficient
uniformity, all degenerate fibres, the source prime-divisor domain,
arbitrary real intervals, and all boundary cases. The earlier 190
proof modules, all 789 earlier export records, the manuscript and PDF,
the verifier, four registered premises, and nine dependency pins remain
unchanged.

**The complete local aggregate verifier passed for all 838 theorem
exports, 199 project Lean modules, and 232 inspected inputs.** It checked
the frozen manuscript and PDF, all numbered statements and the dependency
ledger, the full build, every project module under strict settings, and
every actual theorem type and axiom dependency.

The 789 earlier complete theorem records and all four literature-premise
records are identical to the accepted Lemma 3.9 report. All 49 new complete
types and axiom profiles match the independent export audit. The 232 input
hashes match the frozen checked candidate, and all 28 changed files were
preserved throughout verification. The earlier 190 proof modules and nine
dependency pins are unchanged.

- [Local report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/70775d9c614707e135cbea1f03d2a94bebe0cf8e/certification/verification_report.json).
- Local report SHA-256: `e39e55bfe2dbcd4358eb53deb691928fe19c94f1b26a74fb61c69cdc94b1ed63`.
- Local report bytes: 1,238,027.
- Locally checked candidate: `ccb9a0fe7a6119c9419cdd0051da9f2880c21108`.
- Build: `Build completed successfully (3423 jobs).`.
- Current inventory: 20 Certified, 0 Partial, 0 Active, 22 Pending.
- All 33 supplementary groups remain Pending; whole-paper certification
  remains false.

The report's generation timestamp is its initialization before Lean
execution, not the completion time.

**Independent GitHub verification passed for the exact published
proof commit [70775d9c6147](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/70775d9c614707e135cbea1f03d2a94bebe0cf8e).**
[Run 43750306023, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43750306023) completed
successfully, and every verification-job step succeeded.

- Published proof tree: `8e9394dd729dc11219ab7e6890da8ef73f100dcb`.
- Verification job: `132922568789`; artifact: `14176209696`.
- [Preserved CI report](certification/ci/run_43750306023_attempt_1.json), 1,238,732 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43750306023_attempt_1.zip), 145,236 bytes.
- ZIP SHA-256: `2a09bf10b847d4786253e86b8b64f9d729f096ea7dce1fa539d2569b40a04c6f`.
- CI report SHA-256: `300e24c963bb18db0a6ee5b5697b003dc1434e73092c3bf121e7abb1a85f7c4e`.

The original ZIP digest matches GitHub's recorded digest. Independent
comparison matches the local and CI reports on all 18 verification-content
fields, including 838 complete theorem records, 232 inspected input hashes,
four unchanged literature-premise records, and nine dependency revisions.
All inspected files match the exact published proof commit. The only
execution-specific fields are the generation timestamp and build log.
Earlier records below retain their historical scopes.

<!-- END LEMMA_2_4_VERIFICATION -->

**Lemma 2.5 and Corollary 2.6 are Certified relative to the accepted literature
inputs.** The first is matched to the cited simple-root univariate Weil bound.
The second is proved under the literal manuscript hypotheses, with the
projective charts, affine polynomial, degree, and geometric-root deductions
checked in Lean.

**Lemmas 4.2 and 4.3 are Certified.** The conic parametrization uses one tuple of actual binary quadratic
forms over every field extension. The plane-section estimate uses the literal
geometric rank-three hypothesis and the actual projective character sum.
Their earlier local and GitHub verification evidence is preserved below.

**Lemma 2.7 is Certified.**
The preceding Katz milestone includes the literal quadric geometry, the exact
coefficient, and the scalar bound. The full local verifier passed. GitHub
Actions verification also passed at the exact proof commit recorded below.

**Lemma 5.9 is Certified.** Its final integer and complex trace theorems
derive finiteness of the actual bad-prime set from characteristic-zero
smoothness, then use the literal `p ∤ N_G` hypothesis to prove integrality,
divisibility by `p`, and the bound `|a_p(G)| ≤ 4p`. No separate finiteness
or good-reduction hypothesis remains.

**Lemma 4.1 is Certified.** Part (i) proves finiteness of the actual bad-prime
set and `N_G ≤ K H_G^C`, with constants fixed before `G`. Part (ii) now
constructs `D_p ≠ 0`, proves `D_p(0)=0`, and bounds its degree by `E`
chosen before both `G` and `p`. Nonvanishing implies `F*(u) ≠ 0` and the
literal geometric rank-three condition.

**Lemma 4.4 is Certified.** Its three weight properties, full pointwise
Fourier estimate, and exact zero-frequency identity are proved for the
actual integral data under the literal `p ∤ N_G` hypothesis. The uniform
theorem chooses `E ≥ 1` before `G,p`, then `D_p` before the character.
The elementary section count is proved for every nonzero normal, including
tangent and singular sections. Theorem 1.1 and Theorem 1.4 remain Pending.

**Lemma 4.5 is Certified.** All three clauses are proved for the actual
diagonal forms: characteristic-zero smoothness, geometric bad reduction
at `p ∤ N_F` if and only if `p ∣ M`, and the exact formula
`N_G = rad(|2αM|)` for the existing modulus. Finiteness follows directly
from `M ≠ 0`; no Lang or other literature premise is used.

**Lemma 4.6 is Certified relative to the accepted Weil input.** Its
complete integral theorem proves the exact pencil formula, the literal
integer projective-trace identity, and the generic Fourier bound
`2p^(3/2)+4p`. The prime hypothesis is precisely `p ∤ 2αM`, and the
generic condition is precisely `p ∤ F*(u)u₁u₂u₃u₄`. The exact formula
and trace use only the standard foundations; the bound additionally uses
the existing Weil premise. All Section 4 lemmas are now complete.
Theorem 1.3 remains Pending because its global asymptotic is not proved.

**Lemma 3.1 is Certified.** The actual mixed complete sum satisfies both
the CRT factorization and integer unit-frequency invariance. Integer
lift independence, the source's prime-product weights, and the extension
of functions supplied only at primes outside `N` are proved internally.
The identities include modulus one and shared prime factors between `q`
and `c`; the literal gcd condition also permits `t=0` when `qc=1`.
The supporting prime-factor formula for `C_q`, multiplicativity of
`S_c`, and exact prime Fourier bridge are proved. No literature premise
is used.

**Lemma 3.2 is Certified.** For every prime outside the literal
`N_F = 2|det A|`, all three conclusions hold for the actual symmetric
integral matrix: the shifted Gauss evaluation modulo `p^k`, the exact
Ramanujan formula for the existing `S_{p^k}`, and the cardinality of
the actual projective quadric. The final theorem covers every `k ≥ 1`,
every integral frequency, and every integer scalar not divisible by
`p`. The general-matrix prime base case, residue-digit recurrence,
modular inverses, and unit permutation are proved internally. This
branch uses no literature premise.

**Lemma 3.3 is Certified.** The existing complete sum satisfies
`|S_c(u)| ≤ 4 sqrt(|det A|) c³` for every positive modulus and every
integral frequency. The proof covers arbitrary composite moduli,
including modulus one and bad-prime factors. It proves the exact
kernel phase in the squared Gauss norm, bounds the actual residue
kernel through the integer matrix's determinant and range index, and
sums over the actual residue units. The final theorem assumes symmetry
and integer nonsingularity, without a good-prime or nonsquare condition.
No literature premise is used.

**Lemma 3.4 is Certified.** For every prime `p ∤ N`, every `k ≥ 1`,
and every integral frequency, the existing mixed complete sum has the
exact ramified formula with the original supplied weight evaluated at
`adj(A)u` and Ramanujan modulus `p^(k+1)`. Actual residue digits and
orthogonality prove the weighted Gauss extraction, and an actual unit
digit bijection proves `𝒰_(k+1) = p 𝒮_(p,p^k)`. The source radical
condition supplies good reduction; only the nonzero scalar `p` is
cancelled in the final assembly. No nonvanishing assumption on a
character sum, frequency restriction, or literature premise is used.

**Lemma 3.5 is Certified.** Both identities use the literal
`q₁ = gcd(q,c)` and `q₂ = q/q₁`, the actual complete sums, the
original supplied weight product, and the source Dirichlet character.
The good-modulus formula follows from actual prime-power and CRT
assembly. On the dual cone, the second identity holds for every
positive modulus, including bad-prime factors; the proof retains the
possibly zero bad-part sum multiplicatively. Agreement of the Jacobi
coefficient with the supplied character is proved from the source's
good-prime values. No literature premise is used.

**Lemma 3.6 is Certified.** For every real cutoff `X ≥ 1` and
nonzero integral dual value `m = F*(u)`, the actual sum of
`|𝒮_(q,c)(u)|/c³` over positive `c ≤ X` with `gcd(c,q)=q₁` has
the bound `C_(F,ε) |C_(q₂)(u)| q₁² 1_(q₁∣m) (X|m|)^ε`.
The positive constant is chosen before `N`, the local functions,
`q,q₁,q₂`, the frequency, and the cutoff. Actual Ramanujan values,
CRT, the bad-prime bound, finite factor-pair summation, and elementary
divisor/logarithm estimates prove the result. The actual sum is zero
when `q₁ ∤ m`. No literature premise is added or used.

**Lemma 3.7 is Certified.** For a fixed symmetric nonsingular
integral matrix with nonsquare determinant, the actual unweighted
complete sums satisfy
`|Σ_(1≤c≤X, gcd(c,q)=q₁) S_c(u)| ≤ C_(F,ε) X³(Xq)^ε`
on the integral dual cone `F*(u)=0`. The positive constant is chosen
before the positive squarefree factorization `q=q₁q₂`, the frequency,
and every real cutoff `X≥1`, with `(q,N_F)=1`. The actual quadratic
coefficient is proved nonprincipal from the nonsquare determinant.
Periodic cancellation, the exact Möbius/totient rearrangement, and
an exact bad/good factorization preserve cancellation in the modulus
sum. The stronger core theorem also removes squarefreeness.
No literature premise is added or used.

**Lemma 3.8 is Certified.** The actual normalized zero counts modulo
`p^k` converge at every prime, and the literal local complete-sum
series converges absolutely to that real density. At `p ∤ N_F`,
the density is `(1−χ(p)/p²)/(1−χ(p)/p)`, with a proved nonzero
denominator. The corrected product `∏_p (1−χ(p)/p)σ_p` has summable
absolute deviations from one. Its original character and actual
density remain in every bad-prime factor, including a factor that
vanishes. The finite counting identity includes exponent zero,
the prime two, and all bad primes. No literature premise is added or used.

**Lemma 3.9 is Certified.** The actual restricted series converges in
increasing modulus order and equals the original-character singular-series
constant times the reciprocal good densities at primes dividing `q`.
Its literal real-cutoff tail satisfies `C_(F,epsilon) q^epsilon X^(-1+epsilon)`.
The final theorem chooses the positive constant before the supplied
character data, `q`, and `X`. The boundary uses the analytic `LFunction`
at one and a finite corrected Euler comparison. Original bad-prime
character values and possibly zero bad densities are retained.
No literature premise is added or used.

Lemma 3.11 and the separate exact factorization obligation are now complete; the singular-coefficient identity and bound are the next targets.

## Mathematical scope

### Complete Lemma 3.9

The complete endpoint is
[`source_singular_series`](QuaternaryQuadraticForms/SingularSeriesTheorem.lean).
It proves increasing-modulus convergence, the exact identity

$$
\sum_{\substack{c\ge1\\(c,q)=1}}\frac{S_c(0)}{c^4}
=\mathfrak S_F\prod_{p\mid q}\sigma_p^{-1},
$$

and the uniform real-cutoff remainder estimate for every positive
squarefree `q` coprime to `N_F`. Its positive constant is fixed after
`A,epsilon` and before the supplied character data, modulus, and cutoff.
The supporting estimate is stronger: it is uniform in every real shift
`z>=0` and does not require squarefreeness.

The actual Lemma 3.7 supplies coefficient cancellation. Exact Abel
summation and an integrable power majorant prove ordered convergence,
the correctly signed tail identity, and right continuity at zero shift.
Choosing `eta=min(epsilon,1/2)` yields `C=9K` from the coefficient bound.
The finite-tail bridge identifies the floor interval with `X<c<=Y`.

At positive shift, the actual Lemma 3.3 and CRT give absolute convergence
and the Euler product. The shifted local series have uniform summable
domination on nonnegative shifts and tend to the actual counting densities.
The nonsquare determinant proves that the original supplied character is
nonprincipal. Official mathlib supplies its Euler products in `Re(s)>1`,
nonvanishing at `2+z`, and continuity of its analytic `LFunction` at one.

A finite correction over primes dividing `q*N_F` compares the product
with the exponent-two character product. Its denominators are proved
nonzero character Euler factors and `L(2+z,chi)`, never bad densities.
The final removal product inverts only good densities at primes dividing
`q`, whose nonvanishing is proved. Original character values at bad
primes and zero bad densities are preserved. No conditional global series
is represented as an unconditional sum at zero.

The [complete correspondence review](certification/correspondence/singular_series.md)
records all sixteen modules, 82 public exports, actual definitions,
all source clauses, exact quantifier order, and independent reviews.
No new or existing literature premise enters this milestone.

Historical descriptions below retain the scope of their own milestones.
Their then-pending statements do not override the current inventory.

### Complete Lemma 3.8

The complete source endpoint is
[`source_local_density`](QuaternaryQuadraticForms/LocalDensityTheorem.lean).
For a symmetric nonsingular integral matrix $A$, it proves every
local assertion for every prime $p$, followed by absolute convergence
of the corrected product with the original supplied Dirichlet character.

The finite count is the cardinality of all vectors modulo $p^k$
whose actual integral quadratic value is zero modulo $p^k$:

$$
N_{p,k}=\#\{x\bmod p^k:F(x)\equiv0\pmod{p^k}\}.
$$

Composite-modulus additive orthogonality and an explicit partition
of scalar residues into units and multiples of $p$ prove

$$
p^{-3k}N_{p,k}=\sum_{j=0}^{k}\frac{S_{p^j}(0)}{p^{4j}}.
$$

The scalar partition uses actual residue-digit bijections. Removing
one common factor from the scalar coefficient and modulus leaves
exactly $p^4$ vector lifts. This yields the same finite identity as
the source's valuation grouping, with no nonsingularity assumption
needed at this stage. The proof includes $k=0$, with one vector
modulo one and the existing identity $S_1(0)=1$.

The complete Lemma 3.3 supplies the geometric majorant

$$
\left|\frac{S_{p^k}(0)}{p^{4k}}\right|
\le4\sqrt{|\det A|}\,p^{-k}.
$$

Since every prime is at least two, the series converges absolutely,
including at $p=2$ and every prime dividing $N_F$. The finite identity
therefore proves convergence of the actual normalized real counts.
The density is defined from that counting limit; continuity and
uniqueness of limits identify the full complex series with its real value:

$$
\sigma_p=\lim_{k\to\infty}p^{-3k}N_{p,k}
=\sum_{k\ge0}\frac{S_{p^k}(0)}{p^{4k}}.
$$

For $p\nmid N_F$, the already checked prime-power evaluation and the
exact totient formula give the geometric series with ratio $\chi(p)/p$.
Its norm is strictly below one, proving the denominator nonzero and giving

$$
\sigma_p=\frac{1-\chi(p)p^{-2}}{1-\chi(p)p^{-1}}.
$$

Finally, let $E_p=(1-\chi(p)/p)\sigma_p$, the actual factor of
`eq:SF`. At a good prime, the formula proves
$E_p=1-\chi(p)/p^2$ and $|E_p-1|\le p^{-2}$.
The primes dividing the nonzero integer $N_F$ form a finite set,
so comparison with the convergent prime-restricted $p^{-2}$ series proves

$$
\sum_p|E_p-1|<\infty.
$$

This explicit summability proves absolute convergence of the corrected
product and convergence of the product of its norms. Every bad-prime
factor retains the original supplied character and the actual density.
No strict positivity or nonvanishing of those densities is assumed;
a zero exceptional factor is permitted. The good-prime character
agreement is exactly the source's stated Legendre value property.

The nine modules contain 30 public theorem exports. The
[correspondence review](certification/correspondence/local_density.md)
maps the definitions, each proof stage, all four source clauses,
and the boundary cases. Every new export uses only the standard
logical foundations, with no additional literature premise.
Lemma 3.9 and the global analytic conclusions remain Pending.

### Complete Lemma 3.7

The source endpoint is
[`source_cone_modulus_bound`](QuaternaryQuadraticForms/ConeModulusTheorem.lean).
For a fixed symmetric nonsingular integral matrix $A$ with
$\det A$ not a square and every $\varepsilon>0$, it chooses one
constant $C_{A,\varepsilon}>0$ such that

$$
\left|\sum_{\substack{1\le c\le X\\(c,q)=d}}S_c(u)\right|
\le C_{A,\varepsilon}X^3(Xq)^\varepsilon
$$

for every positive squarefree $q=de$ with $(q,N_F)=1$, every
integral vector $u$ satisfying $u^T\operatorname{adj}(A)u=0$, and
every real $X\ge1$. The constant is chosen before $q,d,e,u,X$.
The core theorem `unweightedModulusSum_le_rpow` proves this bound
for every positive factorization $q=de$, without squarefreeness;
the source wrapper retains the manuscript's squarefree hypothesis.

The left side is the norm of the actual complex sum of unweighted
complete sums. The set `gcdModuliUpTo q d ⌊X⌋₊` contains precisely
the positive natural moduli with $c\le X$ and $\gcd(c,q)=d$.
`unweightedCompleteSumValue` agrees with the existing source sum
at every such modulus. Its value at zero only makes the function
total; zero is absent from the summation set. The theorem has no
prime-weight family, auxiliary modulus $N$, constrained Fourier
factor, or normalization by $c^3$.

Put $a=|\det A|$, $P=4a$, $N_F=2a$, and
$r=\omega(N_F)$. The auxiliary coefficient is the actual function

$$
\psi(n)=
\begin{cases}
\left(\dfrac{\det A}{n}\right),&(n,N_F)=1,\\
0,&(n,N_F)\ne1.
\end{cases}
$$

Jacobi identities prove complete multiplicativity,
$|\psi(n)|\le1$, and period $P$. This function defines an actual
Dirichlet character modulo $P$. The standing nonsquare hypothesis
produces a positive good index with Jacobi value $-1$, by removing
square factors, choosing a quadratic nonresidue, applying CRT, and
handling the remaining sign and power-of-two cases. Thus the actual
character is nonprincipal and its period sum is zero. This argument
also covers negative determinants whose absolute values are squares.
Neither a supplied mean-zero condition nor a supplied character
cancellation estimate appears in the final theorem.

Removing complete periods bounds partial sums by $P$. Finite
summation by parts then proves the cubic estimate
$|\sum_{j\le T}\psi(j)j^3|\le2PT^3$. Möbius detection of
coprimality and an exact multiples reindex give the corresponding
bound $2P\tau(M)T^3$ with $(j,M)=1$. The proof uses the fixed
period $4a$, which is sufficient for a constant depending on $A$;
it makes no unproved claim about the primitive conductor.

The actual relative totient expansion is proved in the integral
quotient form

$$
\varphi(dn)=\varphi(d)
\sum_{\substack{h\mid n\\(h,d)=1}}\mu(h)\frac nh.
$$

Exact finite divisor and gcd rearrangements yield

$$
\begin{aligned}
\sum_{\substack{c\le T\\(c,q)=d}}\psi(c)c^2\varphi(c)
={}&\psi(d)d^2\varphi(d)
\sum_{\substack{h\le T/d\\(h,q)=1}}\mu(h)\psi(h)h^2\\
&\quad{}\times
\sum_{\substack{k\le T/(dh)\\(k,e)=1}}\psi(k)k^3,
\qquad q=de.
\end{aligned}
$$

The quotient cutoffs are natural quotients in Lean. This identity
holds without squarefreeness. The zero extension in $\psi$ retains
the good-prime condition automatically. Cubic cancellation and
$\varphi(d)\le d$ give $2P\tau(e)T^3H_T$, hence
$2P\tau(e)X^3(1+\log X)$ at a real cutoff. On the dual cone the
proved good-modulus evaluation is the actual identity
$S_c(u)=\left(\frac{\det A}{c}\right)c^2\varphi(c)$, so this
bound applies to the genuine good-modulus sum.

For arbitrary moduli the bad-supported part $b$ and good part $g$
form an exact finite bijection $c=bg$. The literal gcd condition is
transported to the good part because $(q,N_F)=1$. Actual CRT gives

$$
\sum_{\substack{c\le X\\(c,q)=d}}S_c(u)
=
\sum_{\substack{b\le X\\p\mid b\Rightarrow p\mid N_F}}
S_b(u)
\sum_{\substack{g\le X/b\\(g,q)=d\\(g,N_F)=1}}S_g(u).
$$

Cancellation is retained inside each inner sum before applying the
triangle inequality over $b$. The uniform estimate
$|S_b(u)|\le4\sqrt a\,b^3$ cancels the cubic divided-cutoff factor.
The already proved prime-support count then gives the explicit
intermediate bound

$$
K_A\,\tau(e)X^3(1+\log X)^{r+1},
\qquad
K_A=8P\sqrt a\left(1+\frac1{\log2}\right)^r.
$$

Uniform divisor and logarithm power estimates, together with
$e\le q$, produce the final $X^3(Xq)^\varepsilon$ bound.
The divisor-count loss $\tau(e)$ and period $P$ are valid replacements
for the manuscript's conductor and $2^{\omega(eN_F)}$ factors within
the permitted dependence on the fixed form and $\varepsilon$.

| New module | Public exports | Checked role |
| --- | ---: | --- |
| [PeriodicSumBound](QuaternaryQuadraticForms/PeriodicSumBound.lean) | 1 | Zero-mean periodic partial sums |
| [CharacterCubicBound](QuaternaryQuadraticForms/CharacterCubicBound.lean) | 2 | Natural and real cubic weighted sums |
| [QuadraticCharacterPeriod](QuaternaryQuadraticForms/QuadraticCharacterPeriod.lean) | 10 | Actual good Jacobi coefficient, period, and Dirichlet character |
| [QuadraticJacobiWitness](QuaternaryQuadraticForms/QuadraticJacobiWitness.lean) | 1 | Quadratic nonresidue and CRT witness |
| [QuadraticCharacterNonprincipal](QuaternaryQuadraticForms/QuadraticCharacterNonprincipal.lean) | 3 | Derived nonprincipality and zero period sum |
| [CoprimeCubicBound](QuaternaryQuadraticForms/CoprimeCubicBound.lean) | 5 | Exact Möbius detection and coprime cubic bound |
| [TotientDivisorExpansion](QuaternaryQuadraticForms/TotientDivisorExpansion.lean) | 2 | Actual ordinary and relative totient expansions |
| [DivisorSumReindex](QuaternaryQuadraticForms/DivisorSumReindex.lean) | 3 | Positive finite divisor and gcd rearrangements |
| [ConeTotientReindex](QuaternaryQuadraticForms/ConeTotientReindex.lean) | 1 | Exact gcd-restricted double sum |
| [TotientCancellationBound](QuaternaryQuadraticForms/TotientCancellationBound.lean) | 2 | Harmonic and real logarithm bounds |
| [ModulusSumFactorization](QuaternaryQuadraticForms/ModulusSumFactorization.lean) | 4 | Unique bad/good split and exact complex-sum CRT |
| [ConeModulusFormula](QuaternaryQuadraticForms/ConeModulusFormula.lean) | 2 | Actual good complete sums as twisted totients |
| [ConeModulusBound](QuaternaryQuadraticForms/ConeModulusBound.lean) | 2 | Full divisor/logarithm bound |
| [ConeModulusTheorem](QuaternaryQuadraticForms/ConeModulusTheorem.lean) | 2 | Uniform core theorem and complete source endpoint |

The complete scope includes modulus one, $q=d=e=1$, $X=1$,
nonintegral real cutoffs, zero frequency $u=0$, and arbitrary powers
of bad primes in the summed modulus. Nonsquareness of the original
integer determinant is used to prove cancellation. No positivity
assumption on the determinant or on the quadratic form is added.

The [correspondence review](certification/correspondence/cone_modulus_bound.md)
checks the complete actual endpoint types and every source clause.
All 40 exports use only standard logical foundations; precisely one
uses only `propext` and the other 39 use the standard triplet.
No literature premise is added or used. All 637 earlier support
records are preserved. All 33 auxiliary groups and the global
analytic theorems retain their separate Pending status. Execution
evidence for the complete 677-export aggregate and its exact proof
commit is recorded separately from this mathematical scope.

### Complete Lemma 3.6

The source endpoint is
[`source_generic_modulus_bound`](QuaternaryQuadraticForms/GenericModulusTheorem.lean).
For a fixed symmetric nonsingular integral matrix `A` and each
$\varepsilon>0$, it chooses one positive constant before all varying
source data. With $m=u^T\operatorname{adj}(A)u\ne0$,
$q=q_1q_2$ positive and squarefree, $(q,N)=1$, and
$\operatorname{rad}(N_F)\mid N$, the conclusion is

$$
\sum_{\substack{1\le c\le X\\\gcd(c,q)=q_1}}
\frac{|\mathcal S_{q,c}(u)|}{c^3}
\le C_{A,\varepsilon}\,|C_{q_2}(u)|\,q_1^2\,
\mathbf 1_{q_1\mid m}\,(X|m|)^\varepsilon,
\qquad X\ge1.
$$

The original local functions need only nonzero scalar invariance and
norm at most one. The constant is independent of `N`, that family,
`q,q₁,q₂`, `u`, and the real cutoff. This quantifier order is visible
in the actual theorem type. The source radical condition derives
`q.Coprime (quadraticBadPrimeModulus A)`; the source extension uses
only the supplied functions at primes outside `N` in both actual sums.
The constrained Fourier factor remains the existing sum at `q₂`, and
its possible zero value is included.

**The actual finite sum.** `gcdModuliUpTo q q₁ ⌊X⌋₊` contains exactly
the positive natural moduli below the real cutoff with the source
gcd condition. `normalizedMixedCompleteSum` equals the norm of the
existing mixed complete sum divided by `c³` at every positive modulus;
its zero extension at `c=0` never enters the summation set.
`modulusNormSum` is the literal finite sum of these terms. From
`q=q₁*q₂` and positivity, division by `q₁` recovers the original `q₂`.

**Ramanujan estimates and the indicator.** The actual unit-digit
recurrences prove every positive prime-power Ramanujan value. Their
combination with actual CRT gives

$$|R_n(m)|\le\gcd(n,|m|),\qquad
|R_{dg}(m)|\le d\gcd(g,|m|).$$

For squarefree `d∣g`, a prime dividing `d` occurs at least twice in
`dg`. If it does not divide `m`, the actual Ramanujan sum vanishes.
This proves the shared-factor divisibility support, and the actual
good-modulus formula and bad/good CRT factorization transfer it to
the mixed sum. Consequently `modulusNormSum_eq_zero_of_not_dvd`
proves that the whole left-hand sum is zero whenever `q₁∤m`.
No local norm hypothesis is needed for this vanishing theorem.

**The stronger divisor/logarithm bound.** The existing uniform bound
controls the bad-prime factor `S_b(u)` in `c=b*g`. The weight norm
bound and actual Jacobi trichotomy give

$$
\frac{|\mathcal S_{q,c}(u)|}{c^3}
\le 4\sqrt{|\det A|}\,|C_{q_2}(u)|\,q_1^2
\frac{\gcd(g,|m|)}g.
$$

The factor-pair map is injective because multiplication recovers `c`.
Thus the actual gcd-restricted sum embeds into a finite rectangle of
bad-supported `b` and positive `g`, with nonnegative summands. Actual
factorization vectors bound the number of possible `b` by
$(1+\log X/\log2)^{\omega(N_F)}$. The finite divisor argument and
the harmonic estimate give

$$\sum_{1\le g\le X}\frac{\gcd(g,|m|)}g
\le\tau(|m|)(1+\log X).$$

The resulting `modulusNormSum_le_divisor_log` has one divisor-count
factor, with logarithm exponent `1+ω(N_F)`. This is a stronger
intermediate bound than the manuscript's two-divisor-factor route.
The proof does not require a separate formalization of the displayed
infinite local series in `eq:ramsplit`; no such identity is assumed.
The broader auxiliary group `aux:ramanujan`, including agreement
with the Möbius divisor definition, remains separately Pending.

For every prescribed positive exponent, `divisors_card_le_rpow`
provides a positive constant uniform over all positive integers, and
`one_add_log_pow_le_rpow` provides a positive constant uniform over
all real `X≥1`. Applying them separately to `|m|` and `X` yields
$|m|^\varepsilon X^\varepsilon=(X|m|)^\varepsilon$.
The fixed prime-support exponent and determinant factor depend only
on `A`. The exact zero theorem inserts the divisibility indicator.
This proves the complete source estimate with the required uniformity.

The boundary cases `q=q₁=q₂=1`, `X=1`, and `|m|=1` are included.
The final estimate requires `m≠0`; its supporting Ramanujan gcd
bounds also cover zero frequency. The source weight's zero-value
condition and Fourier stratification bounds are unused. No
Dirichlet character, nonprincipal-character cancellation, or
nonsquare-determinant hypothesis is needed for this absolute bound.

| New modules | Checked role |
| --- | --- |
| [RamanujanPrimePower](QuaternaryQuadraticForms/RamanujanPrimePower.lean), [RamanujanGcdBound](QuaternaryQuadraticForms/RamanujanGcdBound.lean) | Actual prime-power evaluations, global gcd bound, and shared-factor vanishing |
| [MixedSumNormBounds](QuaternaryQuadraticForms/MixedSumNormBounds.lean), [MixedSumGcdBound](QuaternaryQuadraticForms/MixedSumGcdBound.lean) | Source weight norms, exact bad/good CRT, normalized bound, and mixed-sum divisibility support |
| [PrimeSupportCount](QuaternaryQuadraticForms/PrimeSupportCount.lean), [GcdHarmonicBound](QuaternaryQuadraticForms/GcdHarmonicBound.lean) | Actual prime-support count and the finite gcd/divisor/harmonic estimate |
| [ModulusNormSum](QuaternaryQuadraticForms/ModulusNormSum.lean), [FactorizationSumBound](QuaternaryQuadraticForms/FactorizationSumBound.lean) | Real-cutoff source sum and injective factor-pair summation |
| [DivisorPowerBound](QuaternaryQuadraticForms/DivisorPowerBound.lean), [LogPowerBound](QuaternaryQuadraticForms/LogPowerBound.lean) | Uniform bounds for every positive exponent |
| [GenericModulusBound](QuaternaryQuadraticForms/GenericModulusBound.lean), [GenericModulusTheorem](QuaternaryQuadraticForms/GenericModulusTheorem.lean) | Actual finite-sum estimate, exact zero, uniform power bound, and original-source endpoint |

The [source correspondence review](certification/correspondence/generic_modulus_bound.md)
distinguishes the 39 supporting exports from the numbered result and
records the actual theorem types and dependencies. All 39 new exports
use only standard logical foundations; no literature premise is added
or used. Strict compilation and actual inspection have passed. The
full aggregate and exact-proof-commit CI outcomes are tracked separately
in the execution checkpoint.

### Complete Lemma 3.5

[GoodGlobalTheorem.lean](QuaternaryQuadraticForms/GoodGlobalTheorem.lean)
proves the two source theorems `source_mixedCompleteSum_good_modulus`
and `source_mixedCompleteSum_dual_cone`, and bundles them as
`source_good_global_complete_sum`. Let $q\ge1$ be squarefree,
$(q,N)=1$, and $c\ge1$, with the literal source factors

$$q_1=\gcd(q,c),\qquad q_2=q/q_1.$$

For a good modulus the first clause is

$$\mathcal S_{q,c}(u)
=C_{q_2}(u)\,q_1c^2\chi(q_1c)\,
\xi_{q_1}(\operatorname{adj}(A)u)\,
R_{q_1c}(F^*(u)),\qquad(c,N_F)=1.$$

The second clause holds for every positive modulus:

$$\mathcal S_{q,c}(u)
=C_{q_2}(u)\,q_1^2\chi(q_1)\,
\xi_{q_1}(\operatorname{adj}(A)u)\,S_c(u),
\qquad F^*(u)=0.$$

The left-hand side is the existing
`mixedCompleteSum (extendPrimeWeights N ξ) q c A u`. The first factor
on the right is the existing constrained Fourier sum at the actual
quotient `q / q.gcd c`. The dual value is literally
`dotProduct u (A.adjugate.mulVec u)`, and the weight is evaluated at
the actual integral vector `A.adjugate.mulVec u`. Positive moduli are
represented by `NeZero` instances. Modulus one, zero frequency, and
zero values of any of the complete sums are included.

**The original character and supplied weights.**
`GlobalQuadraticCharacter.lean` defines the intermediate complex
coefficient as the actual Jacobi symbol, and proves its value at one,
multiplicativity at positive moduli, prime and prime-power Legendre
values, and square-one value on coprime arguments. The source theorem
accepts an actual `DirichletCharacter ℂ M` and precisely its stated
Legendre values at primes not dividing `N_F`. Prime induction proves
that this supplied character equals the Jacobi coefficient at every
positive modulus coprime to `N_F`. Consequently, the final formulas
contain the original `χ` evaluated at `q₁ c` and `q₁`, respectively.
There is no hypothesis identifying the character at composite moduli;
that agreement is proved internally.

`SourceCompositeWeights.lean` defines `sourceCompositeWeight` as the
literal product of the original supplied functions over the prime
divisors of a modulus coprime to `N`. It proves that this product agrees
with `compositeWeight (extendPrimeWeights N ξ)`. The final right-hand
weight is therefore the source's supplied product, without imposing
any condition on an undefined or excluded-prime function.

**The actual local-to-global assembly.**
`RamanujanMultiplicativity.lean` reindexes the actual unit sum by
`scaledChineseRemainderUnits`. The standard character splits with
unchanged integer frequency, proving

$$R_{mn}(t)=R_m(t)R_n(t)\qquad((m,n)=1).$$

At zero frequency the sum is the actual unit cardinality, hence
$R_n(0)=\varphi(n)$. The identity
$\varphi(dc)=d\varphi(c)$ for `d ∣ c` follows from the proved
totient/gcd product identity, with the zero case handled separately.
In its positive case only the nonzero natural number $\varphi(d)$
is cancelled. No character sum is divided out.

`GoodUnweightedCompleteSum.lean` combines the actual prime-power
formula of Lemma 3.2 with CRT and Ramanujan multiplicativity to prove

$$S_c(u)=\chi(c)c^2R_c(F^*(u))\qquad((c,N_F)=1).$$

The intermediate coefficient is the proved Jacobi representative;
the character agreement described above supplies the source `χ`.
The proof includes the case `c=1`.

`SquarefreeGcdFactors.lean` proves all arithmetic for the source's
actual gcd and quotient: their product is `q`, they are positive and
squarefree, `q₁ ∣ c`, and `(q₂,q₁ c)=1`. It also proves the gcd split
for a squarefree divisor of a coprime product and proves that a
squarefree divisor of a prime power is `1` or that prime.

`SharedSupportCompleteSum.lean` treats squarefree `q ∣ c`. Induction
over positive prime powers and coprime products reduces the prime-power
case to `q=1` or `q=p`, where Lemmas 3.2 and 3.4 give the exact sums.
For `c=mn`, it splits the weight modulus into `gcd(q,m)` and
`gcd(q,n)` and proves coprimality of the full CRT blocks. The literal
CRT formula, character, composite weights, and Ramanujan factors
combine to give the exact coefficient `q c²` and modulus `q c`.
`GoodGlobalCompleteSum.lean` then separates the actual factor
$C_{q_2}(u)$ by CRT and applies that shared-support formula to `q₁`.
This proves the complete good-modulus identity with the literal
source factors, rather than assuming a suitable factorization.

**The dual-cone clause at arbitrary moduli.**
At a good modulus, `ConeCompleteSum.lean` uses `F*(u)=0`,
$R_n(0)=\varphi(n)$, and
$\varphi(q_1c)=q_1\varphi(c)$ to obtain the exact coefficient of
$S_c(u)$. The identity is proved by multiplication of the displayed
factors and does not require nonvanishing of $S_c(u)$.

For every positive modulus, `ModulusPrimeSplit.lean` constructs
positive coprime `b,g` such that `c = b*g`, every prime of `b` divides
`N_F`, and `(g,N_F)=1`. Coprimality of `q` with `N_F` gives `(q,b)=1`
and proves `gcd(q,c)=gcd(q,g)`. Both actual CRT factorizations are then
used:

$$\mathcal S_{q,c}(u)=S_b(u)\mathcal S_{q,g}(u),\qquad
S_c(u)=S_b(u)S_g(u).$$

The good-part cone formula is multiplied by the existing $S_b(u)$.
This factor is retained throughout, so the full identity includes its
possible vanishing and every bad-prime factor in `c`.

`SourceGoodModulus.lean` proves `(q,N_F)=1` from the source radical
condition `primeRadical N_F ∣ N`, `(q,N)=1`, and `A.det ≠ 0`.
Nonsingularity ensures `N_F ≠ 0`, as required by the prime-divisor
characterization of the literal radical. This supplies the good-prime
condition needed for the arbitrary-modulus cone theorem. The final
bundled source theorem assumes symmetry, nonsingularity, the radical
condition, the supplied character's good-prime values, and scalar
invariance of the supplied prime functions.

The identities do not need the weight's value at zero or its norm
bound, the Section 3 exceptional frequency strata, primitivity or a
particular conductor of the supplied character, or nonsquareness of
the determinant. The source's separate `N ≥ 1` condition is unused;
it is not a consequence of `(q,N)=1`, since `q=1, N=0` satisfies
that coprimality condition. The weaker formal assumptions retain both
complete source conclusions.

The [correspondence review](certification/correspondence/good_global_complete_sum.md)
checks both clauses, the exact source character and weight interfaces,
the gcd/quotient factors, and the arbitrary-modulus cone proof.
No literature premise is used.

### Complete Lemma 3.4

[RamifiedCompleteSum.lean](QuaternaryQuadraticForms/RamifiedCompleteSum.lean)
proves `ramified_complete_sum` at the literal quadratic good-prime
modulus and `source_ramified_complete_sum` for the source's supplied
local functions. The latter assumes a symmetric integral matrix with
nonzero determinant, `primeRadical (quadraticBadPrimeModulus A) ∣ N`,
`p ∤ N`, primality of `p`, `k ≥ 1`, and nonzero-scalar invariance of
the supplied function at `p`. For every integral frequency, it proves

$$\mathcal S_{p,p^k}(u)
=\chi(p)^{k+1}p^{2k+1}\,
\xi_p(\operatorname{adj}(A)u)\,
R_{p^{k+1}}(F^*(u)).$$

The left side is the existing `mixedCompleteSum (extendPrimeWeights N ξ)`.
The right side contains the original supplied function
`ξ p Fact.out hpN`, evaluated at
`reduceFrequency p (A.adjugate.mulVec u)`. The character is the actual
complex cast of `legendreSym p A.det`, and the Ramanujan sum is
`integralRamanujanSum (p ^ (k + 1)) (dotProduct u (A.adjugate.mulVec u))`.
Thus the formula uses the exact integral determinant, adjugate,
frequency, and dual value from the source.

`SourceGoodPrime.lean` derives `p ∤ quadraticBadPrimeModulus A`
from the source radical divisibility and `p ∤ N`. The determinant
hypothesis is used: it makes `N_F = 2 |det A|` nonzero, as required
by the proved prime-divisor characterization of the literal radical.
The empty-product radical at zero would not justify that deduction.
The source's separate `N ≥ 1` condition is unnecessary in this
wrapper, since `p ∤ N` already excludes `N = 0`. No good-reduction
condition is left as an extra assumption in the source endpoint.

`WeightedGaussSums.lean` defines the actual weighted inner sum using
canonical integer lifts of residue vectors and their reduction modulo
`p`. Its actual unit sum is the source's

$$\mathcal U_j(u)=\sum_{a\bmod p^j}^{*}\sum_{x\bmod p^j}
\xi_p(x)e_{p^j}(aF(x)+u\cdot x),\qquad j\ge2.$$

Constant weight one recovers the existing integral Gauss and complete
sums through proved bridges. The weight and character in these
definitions use the same canonical representative of every residue
vector; their agreement with the source sums is part of the proof.

`WeightedGaussStationaryPhase.lean` first works at any positive
modulus `m * p` with `p ∣ m`. The actual residue-digit equivalence
reindexes vectors as $y+mz$. The high digit does not change the
weight modulo `p`. Symmetry expands the exact quadratic phase, and
`p ∣ m` makes its quadratic high-digit term divisible by `mp`.
The remaining high-digit phase is

$$e_p((2aAy+u)\cdot z).$$

The four-coordinate character sum is $p^4$ precisely when
$2aAy+u=0\pmod p$, and zero otherwise. This stationary expansion
itself needs neither primality nor nonsingularity. It is an identity
for the actual weighted sum, not a stationary-phase hypothesis.

`WeightedGaussExtraction.lean` applies the actual adjugate to the
stationary equation, obtaining

$$\operatorname{adj}(A)u=-(2a\det A)y\pmod p.$$

At a good prime with $p\nmid a$, the displayed scalar is nonzero.
The supplied scalar invariance therefore identifies the weight on
every surviving residue with $\xi_p(\operatorname{adj}(A)u)$.
Comparison with the constant-weight-one stationary expansion proves

$$\sum_{x\bmod p^j}\xi_p(x)e_{p^j}(aF(x)+u\cdot x)
=\xi_p(\operatorname{adj}(A)u)
\sum_{x\bmod p^j}e_{p^j}(aF(x)+u\cdot x).$$

`WeightedCompleteSum.lean` proves that every actual residue unit's
canonical integer value is not divisible by `p`. It sums the proved
inner identity and applies the complete Lemma 3.2 formula, giving

$$\mathcal U_j(u)=\chi(p)^j p^{2j}\,
\xi_p(\operatorname{adj}(A)u)R_{p^j}(F^*(u))$$

for every $j\ge2$. All unit hypotheses and weight factors in this
assembly are proved for the actual summation parameters.

`PrimePowerUnitDigits.lean` restricts the existing residue-digit
bijection to a genuine equivalence

$$(\mathbb Z/c\mathbb Z)^\times\times\mathbb Z/p\mathbb Z
\simeq(\mathbb Z/pc\mathbb Z)^\times,\qquad(a,t)\mapsto a+c t,$$

valid for positive moduli with $p\mid c$. Its proof identifies the
canonical value with `a.val + c * t.val` and proves the exact
coprimality condition. In `RamifiedUnitLift.lean`, the `t` sum of
the literal phase contributes `p` precisely when $p\mid F(x)$.
That condition is the existing indicator in `mixedIntegerSummand`,
and the weight agrees by the prime specialization of the existing
composite weight. This proves the exact identity

$$\mathcal U_{k+1}(u)=p\mathcal S_{p,p^k}(u).$$

The unit-lift identity needs no symmetry, nonsingularity, parity, or
weight-invariance hypothesis. The final theorem combines it with the
weighted evaluation and cancels only the nonzero complex scalar `p`.
The resulting exponent is exactly `2k+1`, and the Ramanujan modulus
is exactly `p^(k+1)`.

Every $k\ge1$ and every integral frequency is covered, including
$p\mid u$, $p\mid F^*(u)$, and zero frequency. The weight's
vanishing at zero and its norm bound are not needed. Nor does the
proof assume membership in one of the Section 3 exceptional frequency
strata or nonsquareness of the determinant. No character sum or
Ramanujan value is divided out. The
[correspondence review](certification/correspondence/ramified_complete_sum.md)
checks the full source statement and both actual digit arguments.
No literature premise is used.

### Complete Lemma 3.3

[BadPrimeBound.lean](QuaternaryQuadraticForms/BadPrimeBound.lean)
proves `bad_prime_bound` for the manuscript's actual complete sum:

```lean
(c : ℕ) [NeZero c]
(A : Matrix (Fin 4) (Fin 4) ℤ)
(hA : A.transpose = A) (hdet : A.det ≠ 0)
(u : Fin 4 → ℤ) :
  ‖unweightedCompleteSum c A u‖ ≤
    4 * Real.sqrt |(A.det : ℝ)| * (c : ℝ) ^ 3
```

Thus every positive integer modulus and every integral frequency is
covered. The assumptions are precisely symmetry and integer
nonsingularity of the actual matrix. The proof does not impose
nonsingularity modulo `c`, a good-prime restriction, nonsquareness of
the determinant, or a condition on `u`. Modulus one is included.

`GaussNorm.lean` works first over the actual residue ring `ZMod c`.
For an arbitrary symmetric residue matrix and an actual unit parameter,
it proves the exact product identity

$$V_c(a,u)\overline{V_c(a,u)}
=c^4\sum_{\substack{z\bmod c\\2Az=0\pmod c}}
e_c(aF(z)+u\cdot z),$$

where $V_c(a,u)$ is the existing `quadraticGaussSum`. The finite
product of sums is reindexed by the translation $y=x+z$. Symmetry
expands the quadratic phase into its value at `z` and the linear
term $2a\,x^{\mathsf T}Az$. The standard character is primitive at
every positive modulus; separating the four coordinates proves that
the inner sum is `c⁴` exactly on the kernel of `2A`, and zero outside
it. The unit property of `a` proves the exact kernel condition even
when the residue ring has zero divisors.

Taking norms of this proved identity and using the norm-one value of
each character yields

$$|V_c(a,u)|^2\le c^4\#\{z\bmod c:2Az=0\pmod c\}.$$

`MatrixResidueKernel.lean` defines the finite set of vectors killed
by the entrywise reduction of the actual integer `4 × 4` matrix `B`.
`DoubledMatrixKernel.lean` proves that reduction commutes with doubling
and identifies `matrixResidueKernel c (2 • A)` with precisely the
filtered kernel in the Gauss estimate.

`IntegerMatrixKernelBound.lean` proves the determinant bound through
the actual range and index. For `B.det ≠ 0`, the integer map is
injective. Applied to its range and the resulting linear equivalence,
mathlib's proved `Submodule.natAbs_det_equiv` gives

$$[\mathbb Z^4:B\mathbb Z^4]=|\det B|.$$

The library proof uses Smith normal form. Coordinate reduction from
$\mathbb Z^4$ onto $(\mathbb Z/c\mathbb Z)^4$ is proved surjective
using canonical representatives, and it commutes with the integer
matrix map. The image of the integer range is therefore exactly the
range of the reduced matrix. The latter range index divides the
former. For an endomorphism of the actual finite residue group, its
range index equals its kernel cardinality, giving

$$\#K_c(B)\mid|\det B|,\qquad \#K_c(B)\le|\det B|.$$

This provides the kernel estimate needed by the source's Smith
normal-form argument without any coprimality condition on `c`. All
range, reduction, quotient, and kernel identifications are proved for
the actual matrix; the kernel count is not supplied as a hypothesis.

`GaussBoundConstants.lean` proves the exact quaternary identities

$$\det(2A)=16\det A,\qquad |\det(2A)|=16|\det A|.$$

`BadPrimeGaussBound.lean` combines the residue squared-norm inequality
with this integer kernel bound. Taking nonnegative square roots gives

$$|V_c(a,u)|\le4\sqrt{|\det A|}\,c^2.$$

The inner bound is proved both for every actual residue unit and for
integral scalar data whose reduction is a unit. Its integral wrapper
uses the same matrix, coefficient, and frequency reductions as the
source's representative sum.

`CompleteSumNorm.lean` applies the triangle inequality to the existing
`unweightedCompleteSum`, using its already proved identity as the sum
of the actual Gauss sums over `(ZMod c)ˣ`. Injectivity of the unit-value
map proves that there are at most `c` unit parameters, including when
`c=1`. The final `BadPrimeBound.lean` theorem supplies the proved inner
bound to this assembly, yielding the exact factor
$4\sqrt{|\det A|}c^3$. Its final cast identity identifies the natural
absolute determinant with the real absolute value displayed in the
source statement.

The [correspondence review](certification/correspondence/bad_prime_bound.md)
covers the complete statement and the determinant/index realization
of the source argument. All supporting norm and kernel assertions are
proved internally; no literature premise is used.

### Complete Lemma 3.2

[PrimePowerGaussTheorem.lean](QuaternaryQuadraticForms/PrimePowerGaussTheorem.lean)
proves the single source endpoint `prime_power_gauss`. Its hypotheses
are a prime `p`, an exponent `k ≥ 1`, the actual integral symmetric
matrix `A`, the literal condition `p ∤ quadraticBadPrimeModulus A`,
and an arbitrary integral frequency `u`. The existing modulus is
exactly `2 * A.det.natAbs`, so this is $p\nmid N_F=2|\det A|$.
There is no extra diagonalization, recurrence, unit-permutation, or
point-count hypothesis.

Write $\alpha=\det A$, $\chi(p)=(\alpha/p)$, and
$F^*(u)=u^{\mathsf T}\operatorname{adj}(A)u$. The theorem includes
all three source conclusions:

1. For every integer $a$ with $p\nmid a$,

   $$\sum_{x\bmod p^k}e_{p^k}(aF(x)+u\cdot x)
   =\chi(p)^k p^{2k}
   e_{p^k}\!\left(-\overline{4a\alpha}\,F^*(u)\right).$$

2. For the existing unweighted complete sum,

   $$S_{p^k}(u)=\chi(p)^k p^{2k}R_{p^k}(F^*(u)).$$

3. For the actual projective quadric over `ZMod p`,

   $$\#\mathcal Q(\mathbb F_p)=p^2+(1+\chi(p))p+1.$$

The complex coefficient is the cast of `legendreSym p A.det`, raised
to `k`. The phase uses the native inverse in `ZMod (p^k)` of the
reduced integer `4 * a * A.det`, multiplied by the reduction of
`dotProduct u (A.adjugate.mulVec u)`. The cardinality identity is
written in the integers so that the actual Legendre symbol can take
either sign. These are the source's determinant, adjugate dual, and
prime character.

`QuadraticGaussSums.lean` defines the literal residue-vector sums.
`IntegralGaussSums.lean` identifies reduction of the integral data with
the canonical-lift representative formula and the actual inner sum
in the existing `unweightedCompleteSum`. It also proves the
modulus-one Gauss value for every matrix, scalar, and frequency.
`PrimePowerUnits.lean` derives the required units for two, the
determinant, and the scalar from the source divisibility conditions,
without treating `ZMod (p^k)` as a field.

`GeneralPrimeGauss.lean` constructs an actual orthogonal basis over
`ZMod p` for the symmetric matrix. Its change-of-basis matrix `P`
satisfies

$$P^{\mathsf T}AP=\operatorname{diag}(d_i),\qquad
\prod_i d_i=(\det P)^2\det A.$$

Invertibility of the basis matrix and nonsingularity of `A` prove
that every diagonal coefficient is nonzero. Reindexing the finite
sum by this basis and applying the previously checked scalar Gauss
identities gives $V_1(a)=\chi(p)p^2$ for every nonzero scalar. The
zero-scalar value $p^4$ is retained for the later affine count. The
prime theorem applies to a general matrix, with the basis and
determinant-square relation proved internally.

`PrimePowerResidues.lean` constructs actual digit bijections for
positive product moduli, without a coprimality assumption. In
`PrimePowerGaussRecurrence.lean`, the decomposition
$x=r+p(w+mz)$, with $r,z\bmod p$ and $w\bmod m$, gives the exact
phase expansion. Vector additive orthogonality forces the low digit
$r$ to be zero, and the remaining character becomes $e_m(aF(w))$.
For every positive `m`, including one, this proves the actual identity

$$\sum_{x\bmod p^2m}e_{p^2m}(aF(x))
=p^4\sum_{w\bmod m}e_m(aF(w)).$$

Writing $V_k(a)$ for the pure sum at modulus $p^k$, specialization gives

$$V_{k+2}(a)=p^4V_k(a)\qquad(k\ge0).$$

`PrimePowerGauss.lean` combines this recurrence, $V_0(a)=1$, and the
prime base case, using $\chi(p)^2=1$, to obtain
$V_k(a)=\chi(p)^k p^{2k}$. `MatrixSquareCompletion.lean`,
`QuadraticGaussShift.lean`, and `IntegralGaussShift.lean` supply the
actual translation and exact adjugate phase. Both the pure and
shifted integral formulas hold for every $k\ge0$; the final source
endpoint states the requested range $k\ge1$.

The pure formula also holds for every actual residue unit. Its
canonical integral lift is proved nondivisible by `p` by reducing the
unit to `ZMod p`; this step uses `k ≥ 1`.
`RamanujanSums.lean` proves that the reciprocal coefficient map
$a\mapsto-\overline{4a\alpha}$ permutes the actual units.
`GaussRamanujan.lean` and `UnramifiedCompleteSum.lean` then identify
the sum of the shifted phases with the literal Ramanujan unit sum.
No formula for a substitute complete sum is used.

Finally, `QuadricCounting.lean` proves additive orthogonality for the
affine zero set and its relation to the existing projective quadric.
`QuadricPointCount.lean` includes the zero scalar in the Gauss sum,
obtaining

$$\#\{x\in\mathbb F_p^4:F(x)=0\}
=p^3+\chi(p)(p^2-p).$$

Removing the actual origin and counting each projective ray by its
$p-1$ nonzero representatives gives the source's exact projective
count. The final integral wrapper derives symmetry and nonsingularity
of the reduced matrix from the original source assumptions.

The [correspondence review](certification/correspondence/prime_power_gauss.md)
covers every clause of Lemma 3.2 and the source's arithmetic and
geometric objects. This milestone adds no literature premise. It
uses the already checked scalar Gauss identities and does not claim
the separate global analytic conclusions or Lemma 3.3.

### Complete Lemma 3.1

`CompleteSumTheorem.lean` proves `complete_sum_crt` and the final source
wrapper `source_complete_sum_crt`. They concern the existing actual
mixed sum, with the source's integral matrix and frequency and the
literal coprimality condition `(q₁c₁,q₂c₂)=1`. The source wrapper
accepts a local function only for each prime `p ∤ N`, and assumes
`(q₁q₂,N)=1`. Both conclusions are included:

$$\mathcal S_{q_1q_2,c_1c_2}(u)=
\mathcal S_{q_1,c_1}(u)\mathcal S_{q_2,c_2}(u),$$

$$\mathcal S_{q,c}(tu)=\mathcal S_{q,c}(u)
\qquad\text{for every integer }t\text{ with }\gcd(t,qc)=1.$$

`CompositeWeights.lean` defines the actual product
`ξ_q(x)=∏_{p∣q} ξ_p(x mod p)`, with `ξ_1=1`. It proves periodicity,
compatibility with residue lifts and coefficient reduction, factorization
on coprime moduli, and invariance under a unit scalar. The invariant
predicate only concerns primes dividing the specified `q`.
`SourceWeights.lean` extends the supplied good-prime family by zero at
other indices and proves that this extension agrees with every factor
used when `(q,N)=1`. No property at an excluded prime is assumed.

`CompleteSums.lean` defines `mixedCompleteSum`,
`unweightedCompleteSum`, and `constrainedFourierSum` as their literal
finite sums. The mixed sum is over units modulo `c` and vectors modulo
`qc`, constrained by `q ∣ F(x)`, with phase `e_{qc}(aF(x)+u·x)`.
The quadratic value is `dotProduct x (A.mulVec x)`, proved equal to
evaluation of the actual matrix quadratic polynomial.

The canonical representatives in the definition introduce no extra
choice hypothesis. Changing a vector lift modulo `qc` preserves the
weight, congruence condition, and phase. Changing the representative
of `a mod c` changes `aF(x)` by a multiple of `qc`, because the summation
condition is `q ∣ F(x)`. The mixed-phase proof checks this divisibility
before applying the actual standard additive character.

`CRTArithmetic.lean` builds actual residue, unit, and vector bijections
from mathlib's Chinese remainder equivalence. Their forward maps are
the source's scaled coordinates `x=n₂x₁+n₁x₂` and
`a=c₂a₁+c₁a₂`, where `n_i=q_i c_i`. `CRTCharacters.lean` proves
`e_{mn}(nz)=e_m(z)` and
`e_{mn}(na+mb)=e_m(a)e_n(b)` for positive arbitrary moduli, including
one. `MixedPhase.lean` proves the exact source quadratic phase split.
`CompleteSumCRT.lean` combines these with the prime-product weight and
the quadratic-congruence split, then reindexes the local units by
`c₂n₂` and `c₁n₁` to prove the actual double-sum product.

The required coprimality is between the two complete CRT blocks.
There is no assumption `(q,c)=1`; a prime may divide both `q_i` and
`c_i` within a block. The argument in fact needs neither squarefreeness
nor nonsingularity for the two main identities. The source's additional
hypotheses therefore specialize the proved theorem without adding an
unproved implication.

`CompleteSumInvariance.lean` proves the second clause by reindexing
vectors with an inverse of `t` modulo `qc` and units with multiplication
by `t²` modulo `c`. Its final hypothesis is exactly
`t.gcd ((q*c : ℕ) : ℤ)=1`. Negative scalars are included. At modulus
`qc=1`, the residue and unit types are singletons, the sum equals one,
and the same gcd condition permits `t=0`. No global assumption
`t ≠ 0` is introduced.

`CompleteSumSpecializations.lean` proves
`𝒮_{1,c}=S_c`, `𝒮_{q,1}=C_q`, and
`C_1=S_1=𝒮_{1,1}=1`. Its prime theorem identifies `C_p` with the
actual sum on the finite-field quadratic cone. For a polynomial-character
weight, this is exactly the already checked `integralFourierSum`, with
matching coefficients, frequency, and standard additive character. The
bridge itself needs no homogeneity or character-order hypothesis.

`CompleteSumFactorization.lean` proves multiplicativity of `S_c` in
coprime moduli and the squarefree formula

$$C_q(u)=\prod_{p\mid q}C_p(u).$$

The finite-product induction uses invariance only at primes dividing
`q`, and the empty product handles `q=1`. These remain supporting
exports; the separate auxiliary groups are not thereby certified.
The [source correspondence review](certification/correspondence/complete_sum_crt.md)
records both source clauses, the representative choices, modulus-one
cases, source-family extension, and exact connection to the earlier
Fourier branch. All 66 new exports use only standard Lean foundations.

### Complete Lemma 4.6

`DiagonalPencilTheorem.lean` proves the final all-clauses theorem
`diagonal_pencil` for integral vectors `a,b,u` under the literal hypothesis
`¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b`. The actual
sum is the existing `integralFourierSum` for `Matrix.diagonal a`, the
complex quadratic character, and the polynomial of `Matrix.diagonal b`.
The statement reduces the formal integral `Φ_u` polynomial and the
integral `κ_i,ν_i` values into `ZMod p`; its singular filter uses literal
integer divisibility `p ∣ u_i`.

The exact formula is

$$C_p(u)=p\sum_{t\notin\{t_1,t_2,t_3,t_4\}}\chi_p(-\Phi_u(t))
 +p\sum_{i:\,p\mid u_i}\chi_p(\kappa_i)R_p(\nu_i(u)).$$

`DiagonalPencil.lean` defines the source's actual pencil data, including
`κ_i = −a_i ∏_{j≠i}(a_i b_j−a_j b_i)`, and proves their compatibility
with coefficient maps. `DiagonalPencilCubic.lean` identifies the cubic
coefficient with evaluation of the actual adjugate matrix polynomial
and identifies `Φ_u(t)` with the dual form of `G+tF`.
`DiagonalPencilAlgebra.lean` proves distinctness of the four singular
parameters, deduces `5 ≤ p`, and proves the regular and singular
identities. In particular,
`−Δ_i = κ_i/a_i⁴` and `w_i = ν_i/(a_i²Δ_i)` have their literal source
signs and denominators.

`PrimeQuadraticGauss.lean` derives the scalar prime-field identities
from proved mathlib Gauss-sum and square-root counting results. Its
exports cover nonvanishing of `τ_p`, `τ_p²=χ_p(−1)p`, `τ_p⁴=p²`,
Gauss inversion including zero, inversion over units, and the two
square-completion branches. `PrimeRamanujan.lean` defines the actual
finite sum and proves its values `p−1` and `−1`, together with the
unit-scaling and reciprocal-parameter invariances. These statements
use no registered external premise.

`FourierOrthogonality.lean` and `FourierGaussExpansion.lean` express
the actual constrained Fourier sum as the product of four scalar
quadratic exponential sums. The Gauss parameter is a unit before the
substitution `v=s t` or inversion. `DiagonalPencilEvaluation.lean`
computes every regular and singular contribution.
`DiagonalPencilFormula.lean` splits the finite parameter set and
cancels the nonzero factor `p τ_p` to prove the exact formula. Singular
terms with `ν_i(u)=0` remain present; no uniform size-`p` assertion is
made for those terms.

At zero frequency, the regular contribution vanishes and every
Ramanujan value is `p−1`. `DiagonalPencilConsequences.lean` combines
this with the existing exact zero-frequency identity and cancels
`p−1` to obtain the actual complex trace and integer trace. The final
integral identity is

$$a_p(G)=p\sum_i\chi_p(\kappa_i).$$

For the generic bound, `DiagonalPencilReduction.lean` derives all
nonzero coordinate and dual-value hypotheses from
`p ∤ F*(u)u₁u₂u₃u₄`, where `F*(u)` is the actual integral adjugate
quadratic value. The singular sum is empty and `Φ_u` has degree three.
`CubicCharacterSum.lean` handles the separable case using the existing
Weil premise. Over the perfect prime field, a nonseparable cubic is
factored as `c (X−a)²(X−b)` and its actual sum is evaluated internally.
Thus no separability hypothesis is added. The sum over all parameters
has norm at most `2√p`; deleting four parameters gives `2√p+4`, and
multiplication by `p` gives the literal source bound

$$|C_p(u)|\le2p^{3/2}+4p.$$

The four exports in `DiagonalPencilTheorem.lean` give the integral exact
formula, integral projective trace, generic estimate, and conjunction
of all clauses. The formula and trace use only `Classical.choice`,
`Quot.sound`, and `propext`. The generic estimate and all-clauses theorem
add only `QuaternaryQuadraticForms.Trusted.weil_simple_roots`; they use
no Katz, Lang, or Bertini premise. The
[source correspondence review](certification/correspondence/diagonal_pencil.md)
records the full source match. This completes all Section 4 lemmas;
the global asymptotic in Theorem 1.3 remains Pending.

### Complete Lemma 4.5

`DiagonalBadPrimes.lean` proves the final all-clauses theorem
`diagonal_bad_primes`. The integral coefficient vectors `a,b` define
`A = Matrix.diagonal a` and the actual polynomial of `Matrix.diagonal b`.
The hypotheses are `α = ∏ i, a_i ≠ 0` and
`a_i b_j − a_j b_i ≠ 0` for each of the six pairs `i < j`.
`DiagonalForms.lean` proves the formal polynomial identity with
`∑ i, C(a_i) X_i²`, defines the literal product `M`, and proves the
required coefficient-map, nonvanishing, and sign identities.

`DiagonalGeometry.lean` calculates the actual gradient rows and their
two-by-two minors `4 x_i x_j (a_i b_j − a_j b_i)`. In a field of odd
characteristic with nonzero `a_i`, pairwise nonzero determinants imply
the geometric rank-two condition. If the rank failed, the minors would
force at most one nonzero coordinate, contrary to `F(x)=0`.

Conversely, when a pair determinant vanishes, the proof constructs an
actual nonzero point over the algebraic closure: `x_i=1`,
`x_j²=−a_i/a_j`, and all other coordinates zero. An algebraic-closure
square root supplies the coordinate. Both defining polynomials vanish,
and the actual gradient rows are proportional, so their rank is not two.
This establishes the exact field criterion, rather than assuming a
geometric singularity from a numerical surrogate.

`DiagonalReduction.lean` maps the actual equations to the algebraic
closures of `ℚ` and `ZMod p`. It proves `SmoothCharacteristicZero` from
the integral hypotheses and derives odd characteristic and nonzero
reduced `a_i` directly from `p ∤ N_F`. The resulting equivalence is

$$\neg\operatorname{GoodReductionAt}(p,A,G)
\quad\Longleftrightarrow\quad p\mid M
\qquad(p\nmid N_F).$$

The primewise theorem does not additionally assume integral `M ≠ 0`.
It includes `p=3`, zero coefficients `b_i`, and arbitrary signs of the
integer data. No `p ≥ 5` condition enters Lemma 4.5.

`BadPrimeRadical.lean` derives finiteness of the existing bad-prime set
from a nonzero integer with this exact divisibility criterion. Its actual
finset is `primeFactors(|M|) ∖ primeFactors(N_F)`. The disjoint union
with the prime factors of `N_F` therefore proves
`polynomialBadPrimeModulus = primeRadical(N_F * |M|)`. Shared prime
divisors occur once, without a coprimality assumption.

The final diagonal wrapper supplies `M ≠ 0` from the six source hypotheses
and proves the literal identity

$$N_G=\operatorname{rad}(|2\alpha M|).$$

`diagonal_badPrimeModulus` holds for any proof of finiteness passed to
the existing modulus. `diagonal_bad_primes` supplies that proof internally
and combines the smoothness, primewise criterion, and modulus equality.
All 24 new exports have only `Classical.choice`, `Quot.sound`, and
`propext` among their inspected axioms. In particular, the direct
finiteness argument uses no Lang elimination premise. The
[source correspondence review](certification/correspondence/diagonal_bad_primes.md)
records the hypotheses, algebraic-closure witness, signs, and all three clauses.

### Complete Lemma 4.4

`FourierTheorem.lean` proves the final uniform theorem
`uniform_polynomial_fourier_bound`. For a fixed nonsingular symmetric
integral matrix `A` and degree `n ≥ 2`, it chooses `E ≥ 1` before the
integral polynomial `G` and prime `p`. Under the literal homogeneity,
characteristic-zero smoothness, and `p ∤ N_G` assumptions, it chooses a
nonzero `D_p` of degree at most `E`, with `D_p(0)=0` and the dual-form and
geometric rank-three implications from Lemma 4.1(ii). This same polynomial
then works for every nonprincipal character satisfying `ψ ^ n = 1`.

The five conclusions are the three conditions on the actual weight
`x ↦ ψ(G(x))` (value zero at the origin, norm at most one, and invariance
under nonzero scalar multiplication), the bound at every integral frequency,

$$|C_p(u)|\le 2n^2\bigl(p^{3/2}+p^2
\mathbf 1_{D_p(\bar u)=0}\bigr),$$

and the exact identity `C_p(0)=(p−1)a_p(G)`. Here $\bar u$ is the
coordinatewise reduction of `u`; all sums and evaluations are the literal
objects already used in the preceding checked Fourier identities.

`PlaneRestriction.lean` proves the missing geometric step. For any nonzero
normal, its plane has dimension three. If the quadratic restriction
vanished everywhere, polarization in odd characteristic would make the
plane a subspace of its orthogonal complement. Nonsingularity gives that
complement dimension one, a contradiction. An actual linear equivalence
with three coordinates supplies a nonzero ternary polynomial of total
degree at most two and an exact evaluation identity.

`PolynomialGridCount.lean` applies mathlib's proved Schwartz–Zippel theorem
to that polynomial, giving at most `2p²` affine zeros.
`PlaneSectionCardinality.lean` transports the actual zero set through the
coordinate equivalence and proves its cardinality is `1+(p−1)M`, where
`M` counts the actual projective plane-section points. The good-prime
condition gives `p ≥ 3`, so `M ≤ 2p+2`. The proof requires only a nonzero
normal, with no dual-form nonvanishing or section nonsingularity assumption.
Character norms at most one give the literal section-trace bound `2p+2`.

`FourierEstimates.lean` combines the exact ray identity with the checked
Katz and transverse-section estimates. A generic frequency has bound
`2n²p^(3/2)`; every nonzero exceptional frequency has bound `2n²p²`.
The exact zero-frequency identity and Katz estimate give the same
exceptional bound at zero. `FourierBoundConstants.lean` proves all required
constant comparisons and `p^(3/2)=p√p`. `FourierBound.lean` assembles the
indicator estimate and obtains odd characteristic, nonsingular reduction,
and geometric good reduction from the literal `p ∤ N_G` hypothesis.

The final uniform wrapper applies `exceptional_plane_polynomial` before
quantifying over the character, so the exceptional set is independent of
the character and frequency. No restriction `p ∤ n`, extra finiteness
hypothesis, or new literature premise is added. The
[source correspondence review](certification/correspondence/fourier_rays.md)
records every clause, the three frequency cases, and the quantifier order.

### Lang input and the actual bad-reduction system

The previously registered external declaration is
`QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants`, registered
as `EXT.LANG_ELIMINATION`. It is the general generic-coefficient resultant
system in Lang, *Algebra*, revised third edition, IX.4.1, printed p. 402.
The geometric-zero convention follows IX.3.1, p. 389. The
[input review](certification/correspondence/elimination_input.md) records
the arbitrary-field specialization, zero specialized forms, and possibly
empty output family.

The premise chooses finitely many integer polynomials in the independent
coefficients of homogeneous forms before quantifying over the field or
coefficient assignment. Their simultaneous vanishing detects a nonzero
common zero over the algebraic closure. It does not assert any of the
manuscript's rank interpretations, reduction properties, finiteness, or
height bounds.

`HomogeneousForms.lean` proves reconstruction of a homogeneous polynomial
from its literal coefficient vector. `EliminationFamily.lean` substitutes
actual polynomial coefficients into the universal resultant family and
proves that evaluation commutes with this substitution. This polynomial
parameter version is an internal deduction from the generic input.

`RankMinors.lean` and `BadReductionSystem.lean` identify failure of the
rank-two condition with the nonzero common zeros of `F`, `G`, and the
gradient minors. The implementation uses all sixteen ordered minors;
diagonal zero entries and repeated negatives preserve the zero locus of
the manuscript's six minors. The eighteen equations have assigned degrees
`2,n,…,n`, including the zero minors. Homogeneity and coefficient-map
identities are proved over arbitrary commutative rings.

`GenericQuadricFamily.lean` fixes `A,n` and constructs the degree-`n` form
with indeterminate coefficients. `GeometricReduction.lean` identifies the
specializations with the literal rank conditions over the algebraic
closures of `ℚ` and `ZMod p`. Thus `BadReductionResultants.lean` supplies
one fixed integer family `R_j` in the coefficients of `G`: smoothness
selects a nonzero value, and bad reduction at a prime forces every value
to be divisible by that prime. The same selected nonzero integer is
therefore divisible by every actual bad prime. This proves finiteness of
the intrinsic bad-prime set.

### Uniform height bound: complete Lemma 4.1(i)

`PolynomialHeight.lean` defines the actual manuscript height
`max 2 (max |coefficient of G|)` and bounds every integer polynomial
evaluation by its coefficient sum times that height to its total degree.
Taking maxima over the fixed resultant family produces positive constants
`C,K` before `G` is chosen.

`BadReductionHeight.lean` combines that estimate with the nonzero resultant
value. The exact bad-prime product divides its absolute value, so
`N_G ≤ rad(N_F) |z| ≤ K H_G^C`, after absorbing the fixed radical into `K`.
The final theorem quantifies `∃ C K` before `∀ G`; the constants depend
only on the fixed quadratic matrix and degree. It returns a proof that
the actual bad-prime set is finite together with the bound for its literal
modulus. A separate export proves the same bound for every supplied
finiteness proof.

The [source correspondence review](certification/correspondence/bad_reduction.md)
covers the constants' quantifier order and the literal bad-prime modulus.
The following construction completes part (ii), and hence the whole
two-part Lemma 4.1.

### General Bertini input and the geometric plane

The fourth external Lean declaration is
`QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent`, registered
against both `EXT.HARTSHORNE_BERTINI` and `EXT.PROJECTIVE_JACOBIAN`.
This is explicitly a composite interface, documented in the
[source review](certification/correspondence/bertini_input.md).
Hartshorne, *Algebraic Geometry*, II.8.18 and its proof, pp. 179–180,
give the dense open set of regular hyperplane sections. The registered
general projective Jacobian criterion, local dimension, component facts,
and tangent-space interpretation supply its homogeneous-coordinate form.
The corresponding primary-source locators are recorded in that review.

The interface applies to any finite homogeneous system of positive
assigned degrees in `N` coordinates, with `c + 2 ≤ N`, over an
algebraically closed field. Its hypothesis is full rank `c` of the
actual gradient rows at every nonzero common zero. Its conclusion is
a nonzero normal `u` such that, at each common zero on its hyperplane,
there is a common tangent vector `v` with `u·v ≠ 0`. No characteristic-degree
coprimality, irreducibility, or nonemptiness hypothesis is added.

`BertiniPlane.lean` checks the specialization to the actual quadratic
polynomial and degree-`n` form. Pairing a putative linear dependence
with the supplied tangent vector shows that the coefficient of `u`
vanishes; rank two of the two gradients gives rank three after adjoining
`u`. This linear-algebra deduction is internal. The premise contains no
resultant, bad-prime modulus, exceptional polynomial, uniform degree
bound, or Fourier estimate.

### Second elimination system and complete Lemma 4.1(ii)

`RankThreeMinors.lean` proves that rank failure for three rows in four
coordinates is equivalent to vanishing of every ordered three-column
minor. `PlaneReductionSystem.lean` constructs the literal system
`F,G,u·x` and all 64 ordered minors. Zero and repeated minors preserve
the zero locus of the four minors in the manuscript. The 67 equations
have assigned degrees `2,n,1,n,…,n`; their homogeneity and compatibility
with coefficient maps are proved over arbitrary commutative rings.
The geometric common-zero condition is proved equivalent to failure of
the actual `PlaneTransverseRank` predicate.

`ExceptionalPlaneResultants.lean` fixes the integral quadratic matrix and
degree before constructing the joint coefficient and normal parameter
ring. The existing Lang premise, through the checked polynomial-parameter
substitution, supplies one finite family `R_j(g,u)` over the integers.
The same family detects geometric rank failure after every field and
coefficient specialization.

The good-reduction hypothesis permits the proved Bertini specialization
over the algebraic closure. Its transverse-plane witness makes one
resultant evaluation nonzero. `PlaneResultantSpecialization.lean` proves
that an already algebraically closed field has exactly the same common
zeros as its algebraic closure, and that partial coefficient
specialization commutes with field extension. Thus
`S(u)=R_j(G,u)` is a nonzero polynomial over the prime field itself.
The witness need not be rational over that prime field; no such extra
hypothesis is introduced.

`ParameterSpecialization.lean` proves that substitution of polynomials
of degree at most one does not increase total degree.
`ExceptionalPlaneDegree.lean` applies this to specialization of the
coefficients of `G`, retaining the four normal variables. Consequently
`E = 2 + sup_j totalDegree(R_j)` is chosen before `G` and `p`, with
the finite supremum defined to be zero for an empty family.

`ExceptionalPlanePolynomial.lean` constructs the actual product
`D_p = F* S`. Odd characteristic and nonsingularity prove the dual
quadratic polynomial nonzero. The product is nonzero, has degree at most
`E`, and vanishes at the zero normal. If it does not vanish at a normal
`u`, then both `F*(u) ≠ 0` and the full geometric rank-three conclusion
hold. The final theorem starts from characteristic-zero smoothness and
the literal `p ∤ N_G` condition; part (i) supplies the finiteness proof,
and the exact modulus gives odd characteristic, nonsingularity, and
good reduction internally.

These deductions complete every clause of Lemma 4.1(ii). The fixed
resultant family and the uniform degree precede the variable form and
prime in the final theorem types. Neither the generic Bertini premise
nor the Lang premise alone asserts the manuscript's result.

### Katz input and quadric specialization

The previously registered external declaration is
`QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data`. It is a
composite interface for arbitrary smooth geometrically irreducible
hypersurfaces in projective three-space and transverse positive-degree
sections. Katz supplies cohomological concentration, purity, and the trace
formula. The general projective geometry and Jacobian interpretation,
hypersurface adjunction, and degree formula are explicitly included in the
literature boundary, with Fulton and the primary geometric sources recorded
in the [input review](certification/correspondence/katz_input.md).
The interface is registered against `EXT.KATZ` and
`EXT.HYPERSURFACE_CHERN`; these are two source components of one Lean premise.

Its conclusion gives a finite family of complex numbers of norm `p` whose
sum is the actual projective hypersurface character sum. The cardinality is
an unevaluated general Chern coefficient. The premise contains no quadric
specialization, no expanded coefficient `2n²−4n+4`, and no scalar norm bound.
The earlier Weil premise remains separately registered.

`QuadricSmooth.lean` proves that the actual formal gradient is `2 A x`, that
it cannot vanish at a nonzero vector under the matrix hypotheses, and that
these properties persist after coefficient extension. It also proves the
quadratic polynomial irreducible over every extension. A putative product
of affine-linear polynomials would restrict its gradient image to the span
of two fixed vectors and contradict nonsingularity in four dimensions.

`ProjectiveSurfaceTrace.lean` identifies the general hypersurface sum with
the existing literal matrix-quadric trace. It also proves the transverse
polynomial nonzero from an actual nonzero quadric point and the geometric
rank-two hypothesis. Thus none of these required hypotheses is inserted
into the final source theorem as an extra assumption.

`SurfaceChern.lean` works in integer polynomials. From
`coeff_j((1+m*T)*c) = coeff_j((1+T)^4)` for `j ≤ 2`, it proves
`c₀ = 1`, `c₁ = 4−m`, and `c₂ = m²−4m+6`. For `m = 2` it verifies
`c = 1+2T+2T²` and calculates the coefficient `2n²−4n+4`. The finite-sum
triangle inequality then gives the exact bound in Lemma 2.7. No restriction
`p ∤ n` or exact-order character hypothesis is introduced.

### Complete quadratic trace theorem

`QuadraticTraceBound.lean` specializes the Katz estimate to degree two and
the actual quadratic character, proving the integer absolute bound `4p`.
The result is combined with the existing integer/complex trace identity and
prime divisibility. Integral input coefficients are handled using the
literal `GoodReductionAt` condition.

`GoodReduction.lean` defines the exact bad-prime set and the finite product
`N_G = rad(N_F) * product(bad primes)`. It proves
`p ∤ N_G ↔ p ∤ N_F ∧ GoodReductionAt p A G`, with the finiteness proof
kept explicit. It also proves that any nonzero integer divisible by every
bad prime supplies that finiteness, that the bad-prime product divides its
absolute value, and that `N_G ≤ rad(N_F) * |z|`.

`QuadraticTraceTheorem.lean` supplies the final source theorems. It obtains
the finiteness proof from the proved characteristic-zero elimination
argument, then derives odd characteristic, nonsingularity, and good
reduction from `p ∤ N_G`. The integer theorem proves divisibility and the
bound. The complex theorem gives an integer witness equal to the actual
projective character sum, divisible by `p` and of absolute value at most
`4p`. Its only geometric hypothesis is the manuscript's characteristic-zero
rank condition; no finite-set or good-reduction premise is added.

The [quadratic-trace review](certification/correspondence/quadratic_trace.md)
records completion of Lemma 5.9. The final exports use the registered Lang
and Katz inputs, without the separate Weil premise.

### Uniform conic parametrization

The integral wrapper starts from a symmetric integral matrix and the exact
condition `p ∤ 2 |det A|`. The reduction lemmas deduce odd characteristic and
nonsingularity of the reduced matrix, and identify its adjugate with the
reduction of the integral adjugate. Thus the dual-form condition is the
manuscript's `F*(u) ≠ 0`.

The plane restriction is proved nondegenerate and three-dimensional. An
isotropic vector is obtained using official Chevalley–Warning, and a
hyperbolic basis gives the normal form `y₀ y₁ + a y₂²`, with `a ≠ 0`.
The canonical parametrization `(-a s², t², st)` is then embedded into the
original four coordinates as literal multivariate polynomials.

The tuple is chosen over the prime field before quantifying over an extension
field. Mapping its coefficients preserves the linear embedding, its range
equal to the hyperplane, and the normal-form identity. This proves the
required projective bijection over every field containing the prime field.
The equivalence is explicitly identified with polynomial evaluation on every
nonzero representative, and the two vectors of actual formal partial
derivatives are proved linearly independent.

The defining identities are polynomial identities. In particular, the
quadratic coordinate identity is proved before substitution of the quadratic
parametrization. The proof does not infer a degree-four polynomial identity
solely from its values on a small finite field. No conic parametrization,
isotropy, basis, or scalar-extension property is introduced as an external
premise.

### Transverse plane-section estimate

The final theorem accepts rank three for the actual matrix with rows
`∇F(x)`, `∇G(x)`, and `u`, at every nonzero geometric common zero. The formal
chain rule shows that a singular projective zero of `G ∘ μ` would force all
three rows to annihilate two independent derivative vectors. The dimension
contradiction proves nonsingularity of the binary pullback.

The pullback is homogeneous of degree `2n`. Its nonsingularity excludes the
zero polynomial and proves exactly `2n` distinct projective zeros over the
algebraic closure. The affine chart and the point at infinity are both
handled. Euler's identity is used without division by the degree, so the
argument does not require `p ∤ n` or `p ∤ 2n`.

The literal projective section trace is transported along the constructed
bijection. Homogeneity and `ψ ^ n = 1` prove that its character weight is
independent of representative. Corollary 2.6, applied in degree `2n`, gives
the manuscript's bound `(2n−1)√p+1`. The final wrapper constructs both the
base-field and algebraic-closure parametrizations from Lemma 4.2; neither is
an additional hypothesis of Lemma 4.3.

### Previously checked Weil and projective-line input

The registered source input is [K, equation (1.2)], verified against the
matching multiplicative-character estimate on page 1 of Katz's author
version. Its assumptions are a nonprincipal character extended by zero,
a positive-degree polynomial, and degree-many distinct geometric roots.
There is no condition that the degree be prime to p. This published estimate
is assumed under the author's source-relative program, not reproved.

The projective-line deduction constructs an actual equivalence between
projective points and the affine chart together with infinity. Homogeneity
and the character-order condition prove representative independence. The
polynomial is the literal substitution g(X,1), with degree at most n and
with top coefficient g(1,0).

Counting the actual geometric projective zeros proves that the affine
degree is n or n−1 according to whether infinity is a zero, and that all
affine roots are distinct. Since n≥2, the affine degree is positive. Applying
the registered Weil input and adding the character value at infinity gives
the complete bound (n−1)√p+1.

The counting argument replaces the manuscript's intermediate polynomial
divisibility discussion. No simple-root condition or degree conclusion is
assumed as an internal premise.

### Checked exports and correspondence

- [Complete Lemma 3.8 with the original source character](QuaternaryQuadraticForms/LocalDensityTheorem.lean).
- [Exact finite prime-power counting identity](QuaternaryQuadraticForms/LocalDensityCounting.lean).
- [Actual local-density limit and absolute series](QuaternaryQuadraticForms/LocalDensityConvergence.lean).
- [Corrected Euler product with every bad factor retained](QuaternaryQuadraticForms/LocalDensityEulerProduct.lean).
- [Complete Lemma 3.8 correspondence review](certification/correspondence/local_density.md).
- [Complete Lemma 3.7 and its uniform source endpoint](QuaternaryQuadraticForms/ConeModulusTheorem.lean).
- [Exact dual-cone divisor/logarithm bound](QuaternaryQuadraticForms/ConeModulusBound.lean).
- [Complete Lemma 3.7 correspondence review](certification/correspondence/cone_modulus_bound.md).
- [Both source clauses of Lemma 3.5](QuaternaryQuadraticForms/GoodGlobalTheorem.lean).
- [Actual Jacobi coefficients and source-character agreement](QuaternaryQuadraticForms/GlobalQuadraticCharacter.lean).
- [Actual Ramanujan multiplicativity and zero frequency](QuaternaryQuadraticForms/RamanujanMultiplicativity.lean).
- [The literal squarefree gcd factors](QuaternaryQuadraticForms/SquarefreeGcdFactors.lean).
- [The constructed bad/good modulus split](QuaternaryQuadraticForms/ModulusPrimeSplit.lean).
- [Unweighted evaluation at every good modulus](QuaternaryQuadraticForms/GoodUnweightedCompleteSum.lean).
- [The complete shared-support formula](QuaternaryQuadraticForms/SharedSupportCompleteSum.lean).
- [The actual good-modulus global formula](QuaternaryQuadraticForms/GoodGlobalCompleteSum.lean).
- [The dual-cone formula at every positive modulus](QuaternaryQuadraticForms/ConeCompleteSum.lean).
- [The original source weight product](QuaternaryQuadraticForms/SourceCompositeWeights.lean).
- [Good moduli from the source radical condition](QuaternaryQuadraticForms/SourceGoodModulus.lean).
- [Complete Lemma 3.5 correspondence review](certification/correspondence/good_global_complete_sum.md).
- [Complete ramified identity: Lemma 3.4](QuaternaryQuadraticForms/RamifiedCompleteSum.lean).
- [Literal weighted inner and complete sums](QuaternaryQuadraticForms/WeightedGaussSums.lean).
- [Actual weighted stationary expansion](QuaternaryQuadraticForms/WeightedGaussStationaryPhase.lean).
- [Adjugate weight extraction](QuaternaryQuadraticForms/WeightedGaussExtraction.lean).
- [Exact weighted complete-sum evaluation](QuaternaryQuadraticForms/WeightedCompleteSum.lean).
- [Actual unit digits](QuaternaryQuadraticForms/PrimePowerUnitDigits.lean).
- [The exact ramified unit-lift identity](QuaternaryQuadraticForms/RamifiedUnitLift.lean).
- [Good primes from the source radical condition](QuaternaryQuadraticForms/SourceGoodPrime.lean).
- [Complete ramified correspondence review](certification/correspondence/ramified_complete_sum.md).
- [Complete uniform bound: Lemma 3.3](QuaternaryQuadraticForms/BadPrimeBound.lean).
- [Actual Gauss norm and exact kernel phase](QuaternaryQuadraticForms/GaussNorm.lean).
- [The actual residue kernel](QuaternaryQuadraticForms/MatrixResidueKernel.lean).
- [Integer determinant and residue-kernel index bound](QuaternaryQuadraticForms/IntegerMatrixKernelBound.lean).
- [Reduction of the doubled matrix and its kernel](QuaternaryQuadraticForms/DoubledMatrixKernel.lean).
- [Exact determinant, square-root, and unit-count constants](QuaternaryQuadraticForms/GaussBoundConstants.lean).
- [Uniform inner Gauss bound](QuaternaryQuadraticForms/BadPrimeGaussBound.lean).
- [Summation over actual unit parameters](QuaternaryQuadraticForms/CompleteSumNorm.lean).
- [Complete uniform-bound correspondence review](certification/correspondence/bad_prime_bound.md).
- [Complete three-clause Lemma 3.2](QuaternaryQuadraticForms/PrimePowerGaussTheorem.lean).
- [Closed pure and shifted prime-power Gauss formulas](QuaternaryQuadraticForms/PrimePowerGauss.lean).
- [General-matrix prime base case](QuaternaryQuadraticForms/GeneralPrimeGauss.lean).
- [Actual residue digits](QuaternaryQuadraticForms/PrimePowerResidues.lean).
- [Prime-power Gauss recurrence](QuaternaryQuadraticForms/PrimePowerGaussRecurrence.lean).
- [Exact integral adjugate phase](QuaternaryQuadraticForms/IntegralGaussShift.lean).
- [Actual prime-power complete-sum formula](QuaternaryQuadraticForms/UnramifiedCompleteSum.lean).
- [Exact affine and projective quadric counts](QuaternaryQuadraticForms/QuadricPointCount.lean).
- [Complete prime-power Gauss correspondence review](certification/correspondence/prime_power_gauss.md).
- [Complete Lemma 3.1 and its source-family wrapper](QuaternaryQuadraticForms/CompleteSumTheorem.lean).
- [Actual complete sums and lift independence](QuaternaryQuadraticForms/CompleteSums.lean).
- [Mixed CRT factorization](QuaternaryQuadraticForms/CompleteSumCRT.lean).
- [Literal unit-frequency invariance](QuaternaryQuadraticForms/CompleteSumInvariance.lean).
- [Source weight family outside the excluded primes](QuaternaryQuadraticForms/SourceWeights.lean).
- [Modulus-one identities and exact prime Fourier bridge](QuaternaryQuadraticForms/CompleteSumSpecializations.lean).
- [Prime factorization and unweighted multiplicativity](QuaternaryQuadraticForms/CompleteSumFactorization.lean).
- [Complete local-sum CRT correspondence review](certification/correspondence/complete_sum_crt.md).
- [Complete integral Lemma 4.6](QuaternaryQuadraticForms/DiagonalPencilTheorem.lean).
- [Exact finite-field pencil formula](QuaternaryQuadraticForms/DiagonalPencilFormula.lean).
- [Trace and generic Fourier bound](QuaternaryQuadraticForms/DiagonalPencilConsequences.lean).
- [Scalar prime Gauss identities](QuaternaryQuadraticForms/PrimeQuadraticGauss.lean).
- [Literal prime Ramanujan sums](QuaternaryQuadraticForms/PrimeRamanujan.lean).
- [Cubic estimates with repeated roots](QuaternaryQuadraticForms/CubicCharacterSum.lean).
- [Complete diagonal-pencil correspondence review](certification/correspondence/diagonal_pencil.md).
- [Complete Lemma 4.5 and its exact modulus](QuaternaryQuadraticForms/DiagonalBadPrimes.lean).
- [Literal diagonal data and six-factor product](QuaternaryQuadraticForms/DiagonalForms.lean).
- [Diagonal rank criterion and geometric singular point](QuaternaryQuadraticForms/DiagonalGeometry.lean).
- [Characteristic-zero and prime reduction wrappers](QuaternaryQuadraticForms/DiagonalReduction.lean).
- [Direct bad-prime finiteness and radical formula](QuaternaryQuadraticForms/BadPrimeRadical.lean).
- [Complete diagonal bad-prime correspondence review](certification/correspondence/diagonal_bad_primes.md).
- [Complete Lemma 4.4 with uniform exceptional polynomial](QuaternaryQuadraticForms/FourierTheorem.lean).
- [Integral Fourier bound and all five conclusions](QuaternaryQuadraticForms/FourierBound.lean).
- [Actual generic, exceptional, and zero-frequency estimates](QuaternaryQuadraticForms/FourierEstimates.lean).
- [Nonzero plane restriction](QuaternaryQuadraticForms/PlaneRestriction.lean).
- [Affine and projective section counts](QuaternaryQuadraticForms/PlaneSectionCardinality.lean).
- [Complete Fourier correspondence review](certification/correspondence/fourier_rays.md).
- [Complete Lemma 4.1(i)](QuaternaryQuadraticForms/BadReductionHeight.lean).
- [Complete Lemma 4.1(ii)](QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean).
- [Second elimination system and fixed resultant family](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean).
- [General Bertini and projective-Jacobian source review](certification/correspondence/bertini_input.md).
- [Bad-reduction resultant family and finiteness](QuaternaryQuadraticForms/BadReductionResultants.lean).
- [General Lang source review](certification/correspondence/elimination_input.md).
- [Bad-reduction and height correspondence review](certification/correspondence/bad_reduction.md).
- [Complete Lemma 5.9](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean).
- [Quadratic-trace correspondence review](certification/correspondence/quadratic_trace.md).
- [Complete Lemma 2.7](QuaternaryQuadraticForms/KatzBound.lean).
- [Composite Katz/Fulton source review](certification/correspondence/katz_input.md).
- [Quadric Katz correspondence review](certification/correspondence/katz_quadric.md).
- [Quadratic trace bounds](QuaternaryQuadraticForms/QuadraticTraceBound.lean).
- [Exact good-reduction modulus](QuaternaryQuadraticForms/GoodReduction.lean).

- [Complete Lemma 4.2](QuaternaryQuadraticForms/ConicParametrization.lean).
- [Complete Lemma 4.3](QuaternaryQuadraticForms/PlaneSectionTheorem.lean).
- [Uniform conic correspondence review](certification/correspondence/conic_parametrization.md).
- [Plane-section correspondence review](certification/correspondence/plane_section.md).
- [Complete Corollary 2.6](QuaternaryQuadraticForms/ProjectiveWeil.lean).
- [Geometric-root deduction](QuaternaryQuadraticForms/BinaryFormRoots.lean).
- [Projective-line correspondence review](certification/correspondence/projective_weil.md).
- [Exact Weil input review](certification/correspondence/weil_input.md).
- [Inventory with checked-export links](INVENTORY.md).
- [Full dependency graph PNG](docs/dependency_graph.png).
- [Overview PNG](docs/dependency_overview.png).

## Earlier verification evidence

<!-- BEGIN LEMMA_3_9_VERIFICATION -->

The complete Lemma 3.9 milestone adds **82 public theorem exports in
sixteen modules**, bringing the aggregate scope to **789 theorem
exports, 190 project Lean modules, and 222 inspected inputs**.
The final source-theorem target build passed with 3,326 jobs under
official Lean 4.24.0 and the pinned mathlib revision.

All 82 new actual theorem types and axiom dependencies have been
inspected under strict settings. They use only the standard logical
foundations; none uses a literature premise. Independent source review
checked ordered convergence, the literal real-cutoff tail, constant
uniformity, the original character at bad primes, all necessary
nonvanishing, and the boundary limit. The
[source correspondence review](certification/correspondence/singular_series.md)
records the complete argument and its boundary cases.

**The full local aggregate verifier passed for all 789 theorem
exports, 190 project Lean modules, and 222 inspected inputs.** It checked
the frozen source, numbered statements and dependency ledger, the full
build, each project module under strict settings, and every actual
export type and axiom dependency.

All 707 earlier complete theorem records and four literature-premise
records are unchanged. The 82 new records match their independent
actual-type audit; each uses exactly `Classical.choice`, `Quot.sound`,
and `propext`. All 222 input hashes match the checked candidate, and
all 37 frozen changed files were preserved through verification.
The manuscript, PDF, verifier, previous 174 proof modules, and all
nine dependency pins are unchanged.

- [Local report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/20962a741790c681cce4406def550dd44fd8d4d2/certification/verification_report.json).
- Report SHA-256: `6174ae2b7486297ee025ff4ca91dbee47294492ee9d99469928cff26c6d41f24`.
- Report bytes: 1,160,012.
- Locally checked candidate: `44fcc9c14069ed6b4302e5f7dfacb1e55a65d427`.
- Current inventory: 19 Certified, 0 Partial, 0 Active, 23 Pending.
- All 33 supplementary groups remain Pending; whole-paper certification
  remains false.

The report's `generated_at_utc` is its initialization time before Lean
execution. It does not purport to be the completion time.

**Independent GitHub verification passed for the exact published
proof commit [20962a741790](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/20962a741790c681cce4406def550dd44fd8d4d2).**
[Run 43731304257, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43731304257) completed
successfully, and every verification-job step succeeded.

- Published proof tree: `c0121457e890462d679ff04a0014418a17ce0849`.
- Verification job: `132864108708`; artifact: `14168483194`.
- [Preserved CI report](certification/ci/run_43731304257_attempt_1.json), 1,174,125 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43731304257_attempt_1.zip), 136,385 bytes.
- ZIP SHA-256: `9ed668e5cd6b498cf68faeb3843939b34bf796e58a0fefae52e4bb8fe2488859`.
- CI report SHA-256: `e0b43965b4876f8af097cea73646e0234ebabff3b22ed5510a85c0c4a8d60eda`.

The original ZIP digest matches GitHub's recorded digest. Independent
comparison matches the local and CI reports on all 18 verification-content
fields, including 789 complete theorem records, 222 inspected input hashes,
four unchanged literature-premise records, and nine dependency revisions.
All inspected files match the exact published proof commit. The only
execution-specific fields are the generation timestamp and build log.
Earlier records below retain their historical scopes.

<!-- END LEMMA_3_9_VERIFICATION -->

## Earlier Lemma 3.8 execution

<!-- BEGIN LEMMA_3_8_VERIFICATION -->

The current Lemma 3.8 milestone contains 707 theorem exports across
174 project Lean modules and 20 mapped source groups: 30 new public
theorem exports in nine new modules. Its complete aggregate scope
contains 205 inspected inputs, adding those nine modules and
`certification/correspondence/local_density.md` to the preceding
195-input scope. Four registered literature premises and all nine
pinned dependency revisions remain unchanged. Only Lemma 3.8 is
promoted in this milestone; all 33 auxiliary/supplementary groups
remain Pending, and whole-paper certification remains false.

All nine modules passed strict compilation under official Lean
4.24.0 and the pinned mathlib revision, with `warningAsError=true`
and `autoImplicit=false`. The final `LocalDensityTheorem` target
build passed with 3,144 jobs. The unified inspection of all 30 actual
theorem types and axiom lists passed. Every new export uses exactly
`Classical.choice`, `Quot.sound`, and `propext`; none depends on a
literature premise. The source correspondence review and independent
review of the final actual endpoint types cover all four clauses.

The actual-type review checked the original integral quadratic form,
all residue vectors and scalar units, exponent zero, every prime
including two and the bad primes, and the real counting-limit
definition. It also checked the full complex series equality,
absolute norm summability, the proved nonzero good-prime denominator,
and the original supplied character in every corrected product factor.
Summability of the absolute deviations from one is explicit, including
when a bad density vanishes. No finite counting identity, convergence
statement, character-value substitution at bad primes, or analytic
bound remains as an internal premise of `source_local_density`.

### Local-density local execution

**The full local aggregate verifier passed for all 174 project
modules, 707 theorem exports, and 205 inspected inputs.** The resumed
execution completed on 15 November 2026 using official Lean 4.24.0
and the nine pinned dependency revisions. It checked the frozen
manuscript and PDF, all 42 numbered statement identities, the dependency
ledger, the full build, every project module with strict settings,
and the actual declaration kinds, types, and axiom dependencies of
all registered exports and four literature premises.

All 205 input hashes match the frozen candidate. The complete records
of the 677 earlier exports, all four literature inputs, and every
pinned dependency revision are unchanged. The 30 new exports agree
with the separately inspected final types and use exactly the three
standard foundational axioms. Independent review of the source
correspondence and preservation of the preceding proof scope passed.

- [Local report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/eac4b4c9e82470cf142ecd2a4290cfa35a44bf35/certification/verification_report.json).
- Report SHA-256: `0712a8eec668f9f44c87b1c318252ee424004af18f4f50d7bbbbbcc2b2659a56`.
- Published proof commit with identical checked inputs: [eac4b4c9e824](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/eac4b4c9e82470cf142ecd2a4290cfa35a44bf35).
- Published proof tree: `fb189c84421b62195b9c69a0b5f8bf020b487eac`.
- Numbered results: 18 Certified, 0 Partial, 0 Active, 24 Pending.
- All 33 auxiliary/supplementary groups remain Pending.
- Whole-paper certification remains false.

The interrupted predecessor run left an empty output file and is not
used as execution evidence. The saved recovery candidate was restored
without changing its proof inputs; the completed resumed report above
provides the aggregate evidence. Its `generated_at_utc` field records
report initialization before Lean execution, rather than completion.
The earlier 677-export report remains at its immutable proof-commit
link below and retains its original scope.

### Local-density GitHub execution

**The independent GitHub verifier passed for the exact published
proof commit [eac4b4c9e82470cf142ecd2a4290cfa35a44bf35](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/eac4b4c9e82470cf142ecd2a4290cfa35a44bf35).** Its tree is
`fb189c84421b62195b9c69a0b5f8bf020b487eac`, byte-identical to the prepared local
checkpoint `fe2ee69231c00de4233daaaf57907ea73b028938`.

- [Successful run 43725792541, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43725792541).
- Verification job: `132847314315`; every step succeeded.
- Artifact: `14166432952`, 123,921 bytes.
- [Preserved CI report](certification/ci/run_43725792541_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43725792541_attempt_1.zip).
- ZIP SHA-256: `05f9416df22887b06fff84ab49d4a429569f35e8052f6775da1144c27f10cb2a`.
- CI report SHA-256: `ff2b840c83a4604dbb1168a488a71091f8f0b403adeb5defdd82eac7ccaf530a`.
- Local report SHA-256: `0712a8eec668f9f44c87b1c318252ee424004af18f4f50d7bbbbbcc2b2659a56`.

The original artifact was downloaded and its SHA-256 matches the
digest recorded by GitHub. It contains the verification report alone;
the archived ZIP and extracted JSON preserve their exact bytes.

Both comparisons of the local and CI reports matched all 18
verification-content fields, including every one of the 707 complete
theorem records, all four inspected literature-input records, all nine
dependency revisions, all 205 input hashes, and the complete actual-type
and axiom-inspection output. Every input hash also matches the published
proof commit. The generation timestamp and build output are the only
execution-specific fields excluded from the content comparison.

The report records 18 Certified, 0 Partial, 0 Active, and 24 Pending
numbered results. All 33 auxiliary/supplementary groups remain Pending;
whole-paper certification remains false. The evidence archive changes
only README, CHECKPOINT, and the original CI JSON and ZIP. The Lean
sources, status ledger, correspondence review, verifier, frozen
manuscript, and local report remain those of the checked proof commit.

<!-- END LEMMA_3_8_VERIFICATION -->

## Earlier Lemma 3.7 execution

The preceding Lemma 3.7 milestone contained 677 theorem exports across
165 project Lean modules and 20 mapped source groups: 40 new public
theorem exports in fourteen new modules. The completed aggregate report
records 195 input hashes, adding those fourteen modules and
`certification/correspondence/cone_modulus_bound.md` to the 180-input
baseline. Four registered literature premises and all nine pinned
dependency revisions remain unchanged. Only Lemma 3.7 is promoted;
the previous Lemma 3.6 scope note loses its obsolete sentence that
Lemma 3.7 remains Pending.

All fourteen modules passed strict compilation under official Lean
4.24.0 and the pinned mathlib revision, with `warningAsError=true`
and `autoImplicit=false`. The final source-theorem target build passed
with 3,151 jobs. The unified inspection of all 40 actual theorem types
and axiom lists passed. Thirty-nine exports use exactly
`Classical.choice`, `Quot.sound`, and `propext`;
`goodQuadraticChar_coprime_four_iff` uses only `propext`.
No new export depends on a literature premise. The complete source
correspondence review and both final actual endpoint types have
passed review.

### Dual-cone modulus local execution

**The full local aggregate verifier passed for all 165 project
modules and 677 theorem exports.** Every one of the 195 recorded
input hashes matches the checked files. All 40 new full theorem types
and axiom lists match the prior unified inspection. Of these, 39 use
exactly `Classical.choice`, `Quot.sound`, and `propext`;
`goodQuadraticChar_coprime_four_iff` uses only `propext`.
No new export depends on a literature premise.

The independent comparison preserves all 637 preceding complete
theorem records, including actual types, axiom lists, Lean source
hashes, and scopes. It also preserves the 637 prior support records,
all four registered literature premise records, and all nine pinned
dependency revisions. The source-group count remains 20. The only
numbered-result promotion is Lemma 3.7; the earlier Lemma 3.6 scope
note only loses its obsolete sentence that Lemma 3.7 remains Pending.

The exact fifteen added inspected inputs are the fourteen new Lean
modules and `certification/correspondence/cone_modulus_bound.md`.
Only the root Lean import module, `Checks/Exports.lean`,
`certification/status.json`, and
`certification/dependency_inventory.json` changed among the previous
180 inspected inputs; the other 176 previous hashes are unchanged.
All 35 frozen changed-file hashes were preserved during verification,
including the workflow outside the report's 195 input hashes.
The manuscript and PDF remain byte-for-byte unchanged.

The full actual-type audit checked that the positive constant depends
only on the fixed form and positive epsilon, before every varying
modulus, factorization, dual-cone vector, and real cutoff. The source
endpoint retains the squarefree modulus and the literal integral
dual-cone equality. Its conclusion takes the norm after the actual
complex sum over the exact gcd restriction, with power
`C * X^3 * (X*q)^epsilon`. The stronger core omits squarefreeness.
Neither final endpoint assumes a character-cancellation estimate or
any supplied analytic bound. The derived period mean, cubic
cancellation, and divisor-log bound were checked against their full
actual types as well.

The [local verification report at proof commit 5918e83](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/5918e83d0705f4c0ab3b24a3324da18b0ab5e027/certification/verification_report.json)
contains 996,216 bytes and has SHA-256
`17b3f004491f1a6cd601960232f86e467de2bece9d8df6531207a93722b6b4a5`.
It records 17 Certified and 25 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

At that milestone the subsequent README and checkpoint updates recorded
successful local execution without changing any inspected proof input.
The report at that proof commit preserves the exact bytes of the
successfully compared aggregate output; the other 33 frozen paths
were unchanged through that publication.

### Dual-cone modulus GitHub execution

**The full local and GitHub verifiers passed for all 165 modules,
677 theorem exports, four registered premise records, and nine pinned
dependency revisions.** The published proof commit is
[5918e83d0705f4c0ab3b24a3324da18b0ab5e027](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/5918e83d0705f4c0ab3b24a3324da18b0ab5e027), whose tree is `cf6ecf868ee9642f9d9f165091e1ef35152d9fff`.
The same verifier succeeded on the push of that exact proof commit.

- [Successful run 43680979628, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43680979628).
- Workflow: `417945069`; event: `push`; branch: `main`.
- Verification job: `132711319031`; every step succeeded.
- Verification completed `2026-11-15T05:42:09Z`; the job completed `2026-11-15T05:42:12Z`.
- Artifact: `14148294897`, 118,804 bytes, created `2026-11-15T05:42:10Z`.
- [Preserved CI report](certification/ci/run_43680979628_attempt_1.json), 1,008,362 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43680979628_attempt_1.zip).
- ZIP SHA-256: `df9534e5c6360fd3032ad5a82d8379362785cfb2c4d1c29c8551055b5d287424`.
- CI report SHA-256: `9a0621958cc3ad13be370a60dfa571ba777f0d7121160dba0d1346313fed3e0a`.

The original ZIP digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived JSON and both independent report copies. Both strict audits
confirm equality on all 18 verification-content fields: all 677
complete theorem records and their actual types and axiom lists,
four registered premise records, 195 input hashes, nine pinned
dependency revisions, the complete Lean inspection output, the Lean
version, and every verification flag and scope count.
Only `generated_at_utc` and `lake_build_output` differ.

All 637 preceding theorem records remain identical. The complete
actual types and axiom lists of the 40 new exports match the prior
unified inspection: 39 use exactly `Classical.choice`, `Quot.sound`,
and `propext`; `goodQuadraticChar_coprime_four_iff` uses only `propext`.
No new export uses a literature premise. The final actual source type
retains its uniform constant order, nonsquare determinant, literal
integral dual-cone condition, real cutoff, and the norm outside the
actual gcd-restricted complex sum.

At that checkpoint all 195 input hashes matched its inspected files
and the exact proof tree. All 33 frozen nondocument paths, including
the workflow, were checked against their blobs in that same tree.
The accepted local report at that proof commit has 996,216 bytes,
with SHA-256 `17b3f004491f1a6cd601960232f86e467de2bece9d8df6531207a93722b6b4a5`.
The frozen manuscript and PDF were unchanged.

This evidence covers complete Lemma 3.7. Its numbered status was
17 Certified, zero Partial or Active, and 25 Pending; all 33
auxiliary/supplementary groups remain Pending, and whole-paper
certification remains false. Earlier local and CI reports and the
separate interruption-recovery checkpoints retain their own scopes.

This historical Lemma 3.7 execution evidence does not cover the new 707-export Lemma 3.8 milestone.

## Earlier Lemma 3.6 execution

The preceding Lemma 3.6 milestone contained 637 theorem exports across
151 project Lean modules and 20 mapped source groups: 39 new public
theorem exports in twelve new modules. The completed aggregate report
records 180 input hashes, adding those twelve modules and
`certification/correspondence/generic_modulus_bound.md` to the 167-input
baseline. Four registered literature premises and all nine pinned
dependency revisions remain unchanged.

All twelve modules passed strict compilation under official Lean
4.24.0 and the pinned mathlib revision, with `warningAsError=true`
and `autoImplicit=false`. The final source-theorem target build passed
with 3,158 jobs. The unified inspection of all 39 actual theorem types
and axiom lists passed. Every new export uses only standard logical
foundations, without a literature premise.

### Off-dual-cone modulus local execution

**The full local aggregate verifier passed for all 151 project
modules and 637 theorem exports.** Every one of the 180 recorded
input hashes matches the checked files. All 39 new full theorem types
and axiom lists match the prior unified inspection, and all 39 use
exactly `Classical.choice`, `Quot.sound`, and `propext`. No new
export depends on a literature premise.

The independent comparison preserves all 598 preceding complete
theorem records, including actual types, axiom lists, Lean source
hashes, and scopes. It also preserves the 598 prior support records,
all four registered literature premise records, and all nine pinned
dependency revisions. The source-group count remains 20. The only
numbered-result promotion is Lemma 3.6; the earlier Lemma 3.5 scope
note only loses its obsolete sentence that Lemma 3.6 remains Pending.

The exact thirteen added inspected inputs are the twelve new Lean
modules and `certification/correspondence/generic_modulus_bound.md`.
Only the root Lean import module, `Checks/Exports.lean`,
`certification/status.json`, and
`certification/dependency_inventory.json` changed among the previous
167 inspected inputs; the other 163 previous hashes are unchanged.
All 33 frozen changed-file hashes were preserved during verification,
including the workflow outside the report's 180 input hashes.
The manuscript and PDF remain byte-for-byte unchanged.

The full actual-type audit additionally checked that the positive
constant precedes every varying source parameter, the local functions
are supplied only outside `N`, and the endpoint retains the real
cutoff, actual gcd-restricted sum, original constrained Fourier sum,
square factor, divisibility indicator, and exact product power.
The literal zero endpoint and stronger one-divisor logarithm bound
were also checked against their complete printed types.

The [local verification report at proof commit 8acdea4](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/8acdea4a607ce8c59e198373bf2d72daa9a62525/certification/verification_report.json)
contains 942,183 bytes and has SHA-256
`ae070fa70d8f1f02efa7c5e2ee0496d396c7fded6c65fa66ec5946b36d3d90de`.
It records 16 Certified and 26 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

The subsequent README and checkpoint updates at that milestone recorded successful local
execution without changing an inspected proof input. The accepted
report preserved the exact bytes of the successfully compared aggregate
output, and all 31 other frozen paths were checked unchanged.

### Off-dual-cone modulus GitHub execution

**The full local and GitHub verifiers passed for all 151 modules,
637 theorem exports, four registered premise records, and nine pinned
dependency revisions.** The published proof commit is
[8acdea4a607ce8c59e198373bf2d72daa9a62525](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/8acdea4a607ce8c59e198373bf2d72daa9a62525), whose tree is `758abd225eb380a9fd88b7c11ab3097654ff4f46`.
The same verifier succeeded on the push of that exact proof commit.

- [Successful run 43674573868, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43674573868).
- Workflow: `417945069`; event: `push`; branch: `main`.
- Verification job: `132691791438`; every step succeeded.
- Verification completed `2026-11-15T04:12:52Z`; the job completed `2026-11-15T04:12:55Z`.
- Artifact: `14145627876`, 111,239 bytes, created `2026-11-15T04:12:53Z`.
- [Preserved CI report](certification/ci/run_43674573868_attempt_1.json), 953,313 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43674573868_attempt_1.zip).
- ZIP SHA-256: `64f3c79c1818b9a9518966e47c336f2c2e6339a82b7dbc8961faa7d55ce1dcff`.
- CI report SHA-256: `147b132a851d2f4601f1cafc9d7a6b9d65be7bc4d665959512c10b1c2912a61f`.

The original ZIP digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived JSON and both independent report copies. Both strict audits
confirm equality on all 18 verification-content fields: all 637
complete theorem records and their actual types and axiom lists,
four registered premise records, 180 input hashes, nine pinned
dependency revisions, the complete Lean inspection output, the Lean
version, and every verification flag and scope count.
Only `generated_at_utc` and `lake_build_output` differ.

All 598 preceding theorem records remain identical. The 39 new
exports retain exactly `Classical.choice`, `Quot.sound`, and `propext`,
and their complete actual types match the prior unified inspection.
No new export uses a literature premise. The actual source endpoint
retains its uniform constant order and exact arithmetic conclusion.

At that checkpoint all 180 input hashes matched its inspected files and the exact
proof tree. All 31 frozen nondocument paths, including the workflow,
were checked against their blobs in that same tree. The accepted
local report has 942,183 bytes,
with SHA-256 `ae070fa70d8f1f02efa7c5e2ee0496d396c7fded6c65fa66ec5946b36d3d90de`, and equals the report at the proof commit.
The frozen manuscript and PDF are unchanged.

This evidence covers complete Lemma 3.6. The numbered status at that checkpoint was
16 Certified, zero Partial or Active, and 26 Pending; all 33
auxiliary/supplementary groups remain Pending, and whole-paper
certification remains false. Earlier local and CI reports and the
separate interruption-recovery checkpoints retain their own scopes.

This historical execution evidence does not cover the new 677-export Lemma 3.7 milestone.

## Earlier Lemma 3.5 execution

The preceding Lemma 3.5 milestone contained 598 theorem exports across
139 project Lean modules and 20 mapped source groups: 27 new public
theorem exports in eleven new modules. The four registered literature
premises and all nine pinned dependency revisions are unchanged.
Source groups and Lean premise declarations remain separate counts.
The completed aggregate report records 167 input hashes; its twelve
added inputs are the eleven new Lean modules and
`certification/correspondence/good_global_complete_sum.md`.

All eleven modules and the root library passed strict targeted
compilation under official Lean 4.24.0 and the pinned mathlib revision,
with `warningAsError=true` and `autoImplicit=false` (3,180 build jobs).
The combined inspection of all 27 actual theorem types and axiom
lists passed before the aggregate run. Exactly 26 new exports use
`Classical.choice`, `Quot.sound`, and `propext`;
`gcd_mul_blocks_coprime` uses only `propext`. No new export uses a
literature premise.

### Global complete-sum local execution

**The full local aggregate verifier passed for all 139 modules and
598 theorem exports.** All 167 recorded input hashes match the checked
files. All 27 new actual theorem types and axiom lists match their
prior inspections. Exactly 26 exports use the standard foundation
triplet and `gcd_mul_blocks_coprime` uses only `propext`.

The independent comparison confirms that all 571 preceding complete
theorem records remain identical, including actual types, axiom lists,
Lean source hashes, and scopes. All four registered literature premise
records and all nine pinned dependency revisions remain identical to
the preceding report. The mapped source-group count remains 20.

The exact twelve added inspected inputs are the eleven new Lean modules
and `certification/correspondence/good_global_complete_sum.md`. The only
changes to previously inspected inputs are the root Lean import module,
`Checks/Exports.lean`, `certification/status.json`, and
`certification/dependency_inventory.json`. Every one of the 32 frozen
changed-file hashes was preserved through the verification run,
including the workflow, which is outside the report's 167 input hashes.
The frozen manuscript and PDF remain byte-for-byte unchanged.
These subsequent README and checkpoint updates record the successful
local execution; the inspected proof inputs remain those checked by
the aggregate verifier. The installed local report preserves the exact
bytes of the successfully compared verifier output.

The [local verification report at proof commit 5d052df](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/5d052dfa49810e4456dfb6de6e30577493658496/certification/verification_report.json)
contains 879,086 bytes and has SHA-256
`307a164465319d2b0009cc2f3210c6674fbd9783aff81f39c883b55218b3bdeb`.
It records 15 Certified and 27 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### Global complete-sum GitHub execution

**The full local and GitHub verifiers passed for all 139 modules,
598 theorem exports, four registered premise records, and nine pinned
dependency revisions.** The published proof commit is
[5d052dfa49810e4456dfb6de6e30577493658496](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/5d052dfa49810e4456dfb6de6e30577493658496),
whose tree is `c1fc351aa09bac693b50db3d1f45d8f10efec08d`.
The same verifier succeeded on the push of that exact proof commit.

- [Successful run 43648807603, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43648807603).
- Workflow: `417945069`; event: `push`; branch: `main`.
- Verification job: `132612448839`; every step succeeded.
- Verification completed `2026-11-14T22:46:29Z`; the job completed `2026-11-14T22:46:31Z`.
- Artifact: `14134999045`, 103,724 bytes, created `2026-11-14T22:46:30Z`.
- [Preserved CI report](certification/ci/run_43648807603_attempt_1.json), 889,339 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43648807603_attempt_1.zip).
- ZIP SHA-256: `1e75bb6ef4db64e47b391e53cbc5f8751c402509364ed9fc9b30266fbc922a1f`.
- CI report SHA-256: `a0c9710c3554aeb34b82cfbeb8c32e5ef6112833fb3cf28bfbd2e1d10e392119`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON and to the independently extracted report. Both strict
comparisons confirm equality on all 18 verification-content fields:
all 598 complete theorem records and their actual types and axiom
lists, four registered premise records, 167 input hashes, nine pinned
dependency revisions, the complete Lean export-inspection output,
the Lean version, and every verification flag and scope count.
Only `generated_at_utc` and `lake_build_output` differ.

The 27 new exports retain their inspected axiom profiles: 26 use
exactly `Classical.choice`, `Quot.sound`, and `propext`, while
`gcd_mul_blocks_coprime` uses only `propext`. No new export uses a
literature premise.

At that checkpoint all 167 input hashes matched its inspected files
and the exact proof tree. All 30 frozen nondocument paths, including
the workflow, were checked against their blobs in that same tree.
The local report at the published proof commit has
879,086 bytes with SHA-256
`307a164465319d2b0009cc2f3210c6674fbd9783aff81f39c883b55218b3bdeb`.
Those exact bytes are preserved at the published proof commit. The frozen
manuscript and PDF were unchanged. This evidence covers the complete
598-export Lemma 3.5 milestone. Its numbered status was 15 Certified,
zero Partial or Active, and 27 Pending; all 33 auxiliary/supplementary
groups remain Pending and whole-paper certification remains false.
The earlier local and CI reports below retain their original scopes.

## Earlier checked checkpoints

### Ramified milestone

The preceding Lemma 3.4 milestone contained 571 theorem exports across
128 project Lean modules and 20 mapped source groups: 18 new public
theorem exports in eight new modules. The four registered literature
premises and all nine pinned dependency revisions are unchanged.
Source groups and Lean premise declarations remain separate counts.
The completed aggregate report records 155 input hashes; its nine
added inputs are the eight new Lean modules and
`certification/correspondence/ramified_complete_sum.md`.

All eight modules and the root library passed strict targeted
compilation under official Lean 4.24.0 and the pinned mathlib revision,
with `warningAsError=true` and `autoImplicit=false` (3,166 build jobs).
The combined inspection of all 18 actual theorem types and axiom
lists passed before the aggregate run. Each new export uses exactly
`Classical.choice`, `Quot.sound`, and `propext`; no new theorem uses a
literature premise.

### Ramified local execution

**The full local aggregate verifier passed for all 128 modules and
571 theorem exports.** All 155 recorded input hashes match the checked
files. All 18 new actual theorem types and axiom lists match their
prior inspections, with only the three standard foundations in every
new export.

The independent comparison confirms that all 553 preceding complete
theorem records remain identical, including actual types, axiom lists,
Lean source hashes, and scopes. All four registered literature premise
records and all nine pinned dependency revisions remain identical to
the preceding report. The mapped source-group count remains 20.

The exact nine added inspected inputs are the eight new Lean modules
and `certification/correspondence/ramified_complete_sum.md`. The only
changes to previously inspected inputs are the root Lean import module,
`Checks/Exports.lean`, `certification/status.json`, and
`certification/dependency_inventory.json`. Every one of the 28 frozen
changed-file hashes was preserved through the verification run.
The frozen manuscript and PDF remain byte-for-byte unchanged.
These subsequent README and checkpoint updates record the successful
local execution; the inspected proof inputs remain those checked by
the aggregate verifier. The local report at that proof commit preserves
the exact bytes of the successfully compared verifier output.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/169218f4b525d0433c2b53fdd49483f47623c1e8/certification/verification_report.json)
contains 833,730 bytes and has SHA-256
`e0bac7dc8881c3d8837d89fcf5a2b1a37056275256d0f6c8b20a749278e9a734`.
It records 14 Certified and 28 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### Ramified GitHub execution

**The full local and GitHub verifiers passed for all 128 modules,
571 theorem exports, four registered premise records, and nine pinned
dependency revisions.** The published proof commit is
[169218f4b525d0433c2b53fdd49483f47623c1e8](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/169218f4b525d0433c2b53fdd49483f47623c1e8),
whose tree is `008f5c69b8e7d04c4345eea285aa1e571b90cb23`.
The same verifier succeeded on the push of that exact proof commit.

- [Successful run 43641041601, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43641041601).
- Workflow: `417945069`; event: `push`; branch: `main`.
- Verification job: `132588460975`; every step succeeded.
- Verification completed `2026-11-14T21:16:36Z`; the job completed `2026-11-14T21:16:38Z`.
- Artifact: `14131744612`, 98,115 bytes, created `2026-11-14T21:16:37Z`.
- [Preserved CI report](certification/ci/run_43641041601_attempt_1.json), 843,140 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43641041601_attempt_1.zip).
- ZIP SHA-256: `5544d79a2d678768bd00f19c8d55dd17b0dd60d7ec4010facee04f753fd1c2d2`.
- CI report SHA-256: `d6df7af8763ac77898b40940c71b3905c7371b8483f23138a74f53c6a087d0b6`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON and to the independently extracted report. Both strict
comparisons confirm equality on all 18 verification-content fields:
all 571 complete theorem records and their actual types and axiom
lists, four registered premise records, 155 input hashes, nine pinned
dependency revisions, the complete Lean export-inspection output,
the Lean version, and every verification flag and scope count.
Only `generated_at_utc` and `lake_build_output` differ.

All 155 input hashes match the files inspected at that checkpoint and
the exact proof tree. The local report at that published proof commit
contains the exact 833,730 bytes with SHA-256
`e0bac7dc8881c3d8837d89fcf5a2b1a37056275256d0f6c8b20a749278e9a734`.
The original artifact and report were preserved in
[evidence commit 77acba81d1aa6024d8132500464fd66290b2665c](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/77acba81d1aa6024d8132500464fd66290b2665c),
whose tree is `3c3eca9779da8b87d9b3ab844e6c09eb41ae419b`.
The frozen manuscript and PDF are unchanged. This evidence covers the
complete 571-export Lemma 3.4 milestone; it does not cover the subsequent
598-export Lemma 3.5 milestone. At that checkpoint the numbered status
was 14 Certified, zero Partial or Active, and 28 Pending; all 33
auxiliary/supplementary groups were Pending and whole-paper
certification was false. The earlier local and CI reports below
retain their original scopes.

### Uniform bound milestone

The preceding Lemma 3.3 milestone contained 553 theorem exports across
120 project Lean modules and 20 mapped source groups: 17 new public
theorem exports in eight new modules. The four registered literature
premises and all nine pinned dependency revisions are unchanged.
Source groups and Lean premise declarations remain separate counts.
The completed aggregate report records 146 input hashes; its nine
added inputs are the eight new Lean modules and the correspondence
review.

All eight modules and the root library passed strict targeted
compilation under official Lean 4.24.0 and the pinned mathlib revision,
with `warningAsError=true` and `autoImplicit=false` (3,158 build jobs).
All 17 actual theorem types and axiom lists were inspected before the
aggregate run. Each new export uses exactly `Classical.choice`,
`Quot.sound`, and `propext`; no new theorem uses a literature premise.

### Uniform bound local execution

**The full local aggregate verifier passed for all 120 modules and
553 theorem exports.** All 146 recorded input hashes match the checked
files. All 17 new actual theorem types and axiom lists match their
prior individual inspections, with only the three standard foundations
in every new export.

The independent comparison confirms that all 536 preceding complete
theorem records remain identical, including actual types, axiom lists,
Lean source hashes, and scopes. All four registered literature premise
records and all nine pinned dependency revisions remain identical to
the preceding report.

The exact nine added inspected inputs are the eight new Lean modules
and `certification/correspondence/bad_prime_bound.md`. The only changes
to previously inspected inputs are the root Lean import module,
`Checks/Exports.lean`, `certification/status.json`, and
`certification/dependency_inventory.json`. Every one of the 29 frozen
changed-file hashes was preserved through the verification run.
The frozen manuscript and PDF remain byte-for-byte unchanged.
These subsequent README and checkpoint updates record the successful
local execution; the inspected proof inputs remain those checked by
the aggregate verifier. The local report at that proof commit preserves
the exact bytes of the successfully compared verifier output.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/b38301f89b01e424e5cf656da88ea3b56916423d/certification/verification_report.json)
contains 800,979 bytes and has SHA-256
`7760c9e3731c56567d2b0bd83eb2f5a5045acc3b5f93f78693d32084bd3e022d`.
It records 13 Certified and 29 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### Uniform bound GitHub execution

**The full local and GitHub verifiers passed for all 120 modules,
553 theorem exports, four registered premise records, and nine pinned
dependency revisions.** The published proof commit is
[b38301f89b01e424e5cf656da88ea3b56916423d](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/b38301f89b01e424e5cf656da88ea3b56916423d),
whose tree is `ebe28edb7e366b988bc88032f2525be7a507368c`.
The same verifier succeeded on the push of that exact proof commit.

- [Successful run 43637398379, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43637398379).
- Workflow: `417945069`; event: `push`; branch: `main`.
- Verification job: `132577106792`; every step succeeded.
- Verification completed `2026-11-14T20:38:27Z`; the job completed `2026-11-14T20:38:29Z`.
- Artifact: `14130567360`, 94,216 bytes, created `2026-11-14T20:38:28Z`.
- [Preserved CI report](certification/ci/run_43637398379_attempt_1.json), 809,782 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43637398379_attempt_1.zip).
- ZIP SHA-256: `6f13223d4ddc910357e052aee24454d2bfe9ba9e7d96db23a60bda989a9933cf`.
- CI report SHA-256: `85aa7a67cc31680eca5197cfdb759e387076085cf69d54c9883b24dc097a33da`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON and to the independently extracted report. Both strict
comparisons confirm equality on all 18 verification-content fields:
all 553 complete theorem records and their actual types and axiom
lists, four registered premise records, 146 input hashes, nine pinned
dependency revisions, the complete Lean export-inspection output,
the Lean version, and every verification flag and scope count.
Only `generated_at_utc` and `lake_build_output` differ.

All 146 input hashes match the files inspected at that checkpoint and
the exact proof tree. The local report at that published proof commit
contains the exact 800,979 bytes with SHA-256
`7760c9e3731c56567d2b0bd83eb2f5a5045acc3b5f93f78693d32084bd3e022d`.
The original artifact and report were preserved in
[evidence commit 642a0c8064bc3287be3660f132325adab4534624](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/642a0c8064bc3287be3660f132325adab4534624),
whose tree is `91ed8165569569a763e5e9fc364da5e4a17c8657`.
The frozen manuscript and PDF are unchanged. This evidence covers the
complete 553-export Lemma 3.3 milestone; it does not cover the subsequent
571-export ramified milestone or the preceding 598-export Lemma 3.5
milestone. At that checkpoint the numbered status
was 13 Certified, zero Partial or Active, and 29 Pending; all 33
auxiliary/supplementary groups were Pending and whole-paper
certification was false. The earlier local and CI reports below
retain their original scopes.

### Gauss local execution

The preceding Gauss milestone contained 536 theorem exports across 112
project Lean modules and 20 mapped source groups: 54 new public theorem
exports in 16 new modules. The four registered literature premises and
all nine pinned dependency revisions are unchanged. Source groups and
Lean premise declarations remain separate counts. The completed
aggregate report records 137 input hashes; its 17 added inputs are
the 16 new Lean modules and the source correspondence review.

All 16 new modules passed strict targeted builds under official Lean
4.24.0 and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 54 actual theorem types and axiom lists were
inspected before the aggregate run. Each new export uses exactly
`Classical.choice`, `Quot.sound`, and `propext`; no new theorem uses a
literature premise.

**The full local aggregate verifier passed for all 112 modules and
536 theorem exports.** All 137 recorded input hashes match the checked
files. The actual types and axiom lists of all 54 new exports match
their prior individual inspections, with only the three standard
foundations in every new export.

The independent comparison preserves every mathematical field of all
482 preceding exports, including their actual types, axiom lists, and
Lean source hashes. Exactly 472 complete records remain identical.
The other ten are the exports in `PrimeQuadraticGauss.lean`; only their
scope strings change. Each replaces the obsolete sentence that full
prime-power Lemma 3.2 remains Pending with the statement that its
complete prime-power and counting clauses are proved separately.
The comparator checks that exact suffix replacement and permits no
other change to those ten records. All four registered literature
premise records and all nine dependency revisions remain identical
to the preceding report.

The exact 17 added inspected inputs are the 16 new Lean modules and
`certification/correspondence/prime_power_gauss.md`. The only changes
to previously inspected inputs are the root Lean import module,
`Checks/Exports.lean`, `certification/status.json`, and
`certification/dependency_inventory.json`. Every one of the 37 frozen
changed-file hashes was preserved through the verification run.
The frozen manuscript and PDF remain byte-for-byte unchanged.
These subsequent README and checkpoint updates record the successful
local execution; the inspected proof inputs remain those checked by
the aggregate verifier.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/2b3caedb1d46cafcfdc7e47d678bcfc654ef39d7/certification/verification_report.json)
contains 780,870 bytes and has SHA-256
`824069fc67d6f55812e9c9928c1461bb580564b92ee0f7e4cf1b252e59cd0699`.
It records 12 Certified and 30 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### Gauss GitHub execution

**The full local and GitHub verifiers passed for all 112 modules,
536 theorem exports, four registered premise records, and nine pinned
dependency revisions.** The published proof commit is
[2b3caedb1d46cafcfdc7e47d678bcfc654ef39d7](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/2b3caedb1d46cafcfdc7e47d678bcfc654ef39d7),
whose tree is `dea151816197aafb69f94b3d9a7b885a24b63a5d`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43633148645, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43633148645).
- Verification job: `132564011074`; every step succeeded.
- Verification completed `2026-11-14T19:48:39Z`; the job completed `2026-11-14T19:48:43Z`.
- Artifact: `14128654819`, 91,228 bytes, created `2026-11-14T19:48:40Z`.
- [Preserved CI report](certification/ci/run_43633148645_attempt_1.json), 788,811 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43633148645_attempt_1.zip).
- ZIP SHA-256: `0e46e53424a2264c3f0335a81bb9fbdff8bf25016342115213e5af3da6424d90`.
- CI report SHA-256: `403930110d44417d11827c61441cfb4a7e52e4f05f8f56432e0b993e35e9ce71`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON. The local and CI reports agree exactly on all 18
verification-content fields: all 536 complete theorem records and their
actual types and axiom dependencies, four registered premise records,
137 input hashes, nine pinned dependency revisions, the complete Lean
export-inspection output, the Lean version, and every verification flag
and scope count. Only `generated_at_utc` and `lake_build_output` differ.

Every recorded input hash matches the inspected files at that checkpoint
and the exact proof tree. The local report at that proof commit has
780,870 bytes and SHA-256
`824069fc67d6f55812e9c9928c1461bb580564b92ee0f7e4cf1b252e59cd0699`.
The report and original artifact were preserved in
[evidence commit cf3e902](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/cf3e90217e153d04ffd40a9636dceb29fc6fbc59),
whose tree is `d13c6fd8f97143c159254d78c238eb8003ee4273`.
That evidence commit changed only README, CHECKPOINT, and the two
archived CI files; all 137 inspected inputs and the local report were
unchanged. The frozen manuscript and PDF are unchanged. This evidence
covers the preceding 536-export Gauss milestone; it does not cover the
subsequent 553-export bound and 571-export ramified milestones or the
preceding 598-export Lemma 3.5 milestone. At that checkpoint, the numbered status
was 12 Certified, zero Partial or Active, and 30 Pending, with all 33
auxiliary/supplementary groups Pending and whole-paper certification
false. Earlier local and CI reports below retain their original scopes.

### CRT local execution

The preceding CRT milestone contained 482 theorem exports across 96 project
Lean modules and 20 mapped source groups: 66 new exports in 12 new
modules. The four registered literature premises and all nine pinned
dependency revisions are unchanged. Source groups and Lean premise
declarations remain separate counts. The completed aggregate report
records 120 input hashes, including the new correspondence review.

All 12 new modules have passed strict builds under official Lean 4.24.0
and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 66 new actual theorem types and axiom lists
have been inspected. Exactly 65 use `Classical.choice`, `Quot.sound`,
and `propext`; `residueLift_cast` uses only `Quot.sound` and `propext`.
No new theorem uses a registered literature premise. The frozen
manuscript, PDF, and dependency pins remain unchanged.

**The full aggregate local verifier passed for all 96 modules and 482
theorem exports.** All 120 input hashes match the checked files. The
independent baseline comparison confirms that all 416 preceding complete
theorem records are identical, including actual types, axiom dependencies,
source hashes, and scopes. All four registered premise records and all
nine dependency revisions match the preceding report exactly. The 66
new actual theorem types and axiom dependencies match their prior
individual inspections, with no literature premise in any new export.

All 33 changed-file hashes matched the frozen snapshot throughout the
verification run. The 13 added inspected inputs are the 12 new Lean
modules and the source correspondence review. The frozen manuscript
and PDF remain byte-for-byte unchanged. The subsequent README and
checkpoint edits record the successful execution; the inspected proof
inputs remain those checked by the aggregate verifier.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/0224dae194b48080f8af732dbf78580ffaab0c24/certification/verification_report.json)
contains 708,765 bytes and has SHA-256
`ec46cb57a7912faf2116faed95bc6021ed68a9ed78cfb28a05133c0df4515f0f`.
It records 11 Certified and 31 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### CRT GitHub execution

**The full local and GitHub verifiers passed for all 96 modules, 482 theorem
exports, four registered premise records, and nine pinned dependency
revisions.** The published proof commit is
[`0224dae194b48080f8af732dbf78580ffaab0c24`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/0224dae194b48080f8af732dbf78580ffaab0c24),
whose tree is `62ac309aaa1aec3563b46f87e4a881d17a9bc474`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43626335642, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43626335642).
- Verification job: `132542869983`; every step succeeded.
- Verification completed `2026-11-14T18:31:45Z`; the job completed `2026-11-14T18:31:47Z`.
- Artifact: `14127140616`, 82,657 bytes, created `2026-11-14T18:31:46Z`.
- [Preserved CI report](certification/ci/run_43626335642_attempt_1.json), 715,749 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43626335642_attempt_1.zip).
- ZIP SHA-256: `7f343e481201ecbd5d9759d0c97392d0a9104db7894c05226b0dd1d19c8344e3`.
- CI report SHA-256: `72cb4961d00501e3e98a17a1871169548b7d8d70a7f479e9304bd0887a75b56b`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON. The local and CI reports agree exactly on all 18
verification-content fields: all 482 complete theorem records and their
actual types and axiom dependencies, four registered-premise records,
120 input hashes, nine pinned dependency revisions, the complete Lean
export-inspection output, the Lean version, and every verification flag
and scope count. Only `generated_at_utc` and `lake_build_output` differ.

Every recorded input hash matches the inspected files at that checkpoint
and the exact proof tree. The local report is the 708,765-byte report
identified above, byte-identical to the report in that proof commit.
The frozen manuscript and PDF are unchanged. This evidence covers the
preceding 482-export CRT milestone; it does not cover the new
536-export Gauss milestone. The earlier local and CI reports below
retain their original scopes. At the CRT checkpoint, the numbered
status was 11 Certified, zero Partial or Active, and 31 Pending, with
all 33 auxiliary/supplementary groups Pending and whole-paper
certification false.

### Pencil local execution

The preceding pencil milestone contained 416 theorem exports across 84
project Lean modules and 20 mapped source groups: 67 new exports in 13
new modules. The four registered literature premises are unchanged,
as are all nine pinned dependency revisions. Source groups and Lean
premise declarations remain separate counts. The completed aggregate
report records 107 input hashes, including the new correspondence review.

All 13 new modules passed strict builds under official Lean 4.24.0
and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 67 new actual theorem types and axiom
dependencies were inspected. Of these, 59 use exactly
`Classical.choice`, `Quot.sound`, and `propext`; one uses only `propext`;
and seven additionally use the existing registered Weil premise.
The exact pencil formula and both complex and integer trace identities
use only standard foundations. The generic bound adds only Weil.
No new external premise has been introduced, and the Lean, mathlib,
manuscript, and PDF inputs remain fixed.

**The full local and GitHub verifiers passed for all 84 modules, 416 theorem
exports, four registered premise records, and nine pinned dependency
revisions.** All 107 input
hashes match the checked files. The independent baseline comparison
confirmed that all 349 preceding complete theorem records are unchanged,
including their actual types, axiom lists, source hashes, and scopes.
All four registered premise records and all nine dependency revisions
also match the preceding report exactly. The 67 new actual types and
axiom lists match their earlier individual inspections.

At the verification freeze, all 34 changed-file hashes matched the frozen
snapshot. The 14 added inspected inputs are the 13 new Lean modules and
the new source correspondence review. Among the preceding inspected
inputs, only the root Lean imports, `Checks/Exports.lean`,
`certification/status.json`, and `certification/dependency_inventory.json`
changed. The frozen manuscript and PDF remain byte-for-byte unchanged.
The subsequent edits record this successful execution in README and this
checkpoint and preserve the exact report; the inspected proof inputs
remain those checked by the successful aggregate run.

The [local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/7da6aca687135b7c0f859873e69d5fe844b2cdac/certification/verification_report.json)
contains 620,000 bytes and has SHA-256
`d60c7a129061c59979ff52a1b79adca054ed97073fd0a527eb0a6d0663a1dca1`.
It records 10 Certified and 32 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### Pencil GitHub execution

The published proof commit is
[`7da6aca687135b7c0f859873e69d5fe844b2cdac`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/7da6aca687135b7c0f859873e69d5fe844b2cdac),
whose tree is `c78fd84236351f88baabd440f99fc5ca83fd2fc3`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43618745198, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43618745198).
- Verification job: `132519443067`; every step succeeded.
- Verification completed `2026-11-14T17:07:53Z`; the job and run completed `2026-11-14T17:07:56Z`.
- Artifact: `14123891609`, 72,429 bytes, created `2026-11-14T17:07:54Z`.
- [Preserved CI report](certification/ci/run_43618745198_attempt_1.json), 626,114 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43618745198_attempt_1.zip).
- ZIP SHA-256: `f2ff89bd98196e6af865a617631c6a5ee2163c984e78d4834ea56871de895407`.
- CI report SHA-256: `ba6f569e5bd2e93e6893034f2cd514779fd92536479d91ecac4e548ad0754b8c`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON. The local and CI reports agree exactly on all 18
verification-content fields: all 416 complete theorem records and their
actual types and axiom dependencies, four registered-premise records,
107 input hashes, nine pinned dependency revisions, the complete Lean
export-inspection output, the Lean version, and every verification flag
and scope count. Only `generated_at_utc` and `lake_build_output` differ.

Every recorded input hash matched both the inspected files at that
checkpoint and the exact proof tree. Its proof sources, registries, source
reviews, and local report were byte-identical to the checked proof commit.
This evidence covers the complete preceding 416-export pencil milestone;
it does not cover the new 482-export CRT scope. The older local and CI
reports below retain their original scopes.


### Diagonal bad-prime local execution

The preceding diagonal bad-prime milestone registered 349 theorem exports across 71 project
Lean modules and 20 mapped source groups. The four registered literature
premises are unchanged, as are the nine pinned dependency revisions.
Source groups and Lean premise declarations remain separate counts.

Its five new modules passed strict builds under official Lean 4.24.0
and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 24 new actual theorem types and axiom dependencies
were inspected. They use only the standard foundations
`Classical.choice`, `Quot.sound`, and `propext`; no new external premise is
introduced, and the diagonal finiteness proof does not use elimination.

The full aggregate local verifier passed for all 71 modules, 349 theorem
records, four registered literature-input records, and nine pinned
dependency revisions. All 93 recorded input hashes matched the files
checked. Every one of the 325 previously checked theorem records is
unchanged, including the actual types, axiom lists, source hashes and
scopes. The four registered premise records and all dependency revisions
exactly match the preceding local report. The frozen manuscript and PDF
remain unchanged.

The [local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6/certification/verification_report.json)
has SHA-256
`50606c6ea147df96a5905de201f9263396e037299d8ef3a1743c6d325d81a0b8`
and contains 525,699 bytes. It records 9 Certified and 33 Pending numbered
results, with zero Partial or Active results. All 33 auxiliary/supplementary
groups remain Pending, and whole-paper certification remains false.

### Diagonal bad-prime GitHub execution

The published proof commit is
[`09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6),
whose tree is `1930ec532bb7f03a949da69bc49cafb78634c380`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43614640507, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43614640507).
- Verification job: `132506910704`; every step succeeded.
- Verification completed `2026-11-14T16:24:34Z`; the job completed `2026-11-14T16:24:36Z`.
- Artifact: `14121901170`, 62,602 bytes, created `2026-11-14T16:24:34Z`.
- [Preserved CI report](certification/ci/run_43614640507_attempt_1.json), 530,824 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43614640507_attempt_1.zip).
- ZIP SHA-256: `a6ee78b674f2eb0d813e442e67b5d4d0ebac91ae98e26f2d9453db7c1b54dcc9`.
- CI report SHA-256: `a9ca9c083e737b48257fbc01c3225782b61608e4a0ccc932de1d47e6d122cacd`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, and both archived files
are byte-identical to the download and extracted member. The CI and
local reports agree exactly on all 18 verification-content fields:
all 349 full theorem records and their actual types and axiom dependencies,
all four registered-premise records, all 93 input hashes, all nine pinned
dependency revisions, the complete Lean export-inspection output, the
Lean version, and all verification flags and scope counts. The only
differing fields are `generated_at_utc` and `lake_build_output`.

Every recorded input hash also matches the files at the proof commit and
the checked source at that checkpoint. All 24 new export records have only
`Classical.choice`, `Quot.sound`, and `propext` in their axiom lists.
This evidence covers the complete 349-export diagonal bad-prime milestone.
It does not cover the new 416-export pencil scope. The older runs below
retain their original scopes.

### Polynomial Fourier local execution

The preceding polynomial Fourier milestone registered 325 theorem exports across 66 project
Lean modules and 20 mapped source groups. There are four separately
registered external Lean premises: Weil, the composite Katz/Fulton
spectral interface, Lang's general resultants, and the composite Bertini
and projective-Jacobian tangent interface. Source groups and Lean premise
declarations are counted separately.

Its seven new modules passed strict builds under official Lean 4.24.0 and
the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. The final uniform wrapper compiled successfully
without additional assumptions. All 23 new actual theorem types and axiom
dependencies were inspected. Seventeen new helpers use only the
standard foundations `propext`, `Classical.choice`, and `Quot.sound`.
The generic and finite-field indicator bounds use Katz and Weil; the
zero-frequency and nonzero-frequency bounds use Katz. The integral
`fourier_bound` uses Katz, Lang, and Weil. The final
`uniform_polynomial_fourier_bound` uses all four unchanged registered
literature premises, including the construction of its exceptional
polynomial.

The full aggregate local verifier passed for all 66 modules, 325 theorem
records, four registered literature-input records, and nine pinned
dependency revisions. All 87 recorded input hashes matched the files checked
at that checkpoint. Every one of the 302 previously checked theorem types
and axiom lists was unchanged; their source hashes and scopes were also
unchanged. The four registered premise records and all dependency revisions
exactly matched the preceding local report. The frozen manuscript and PDF
were unchanged.

The [local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/25dea299d18e2a423404488ac1a923fded0cde7b/certification/verification_report.json)
has SHA-256
`88f51797dd5b426549a351f4cbc62dc24dd51b5d5c57005298b6ee691edcd003`.
The report records 8 Certified and 34 Pending numbered results, with zero
Partial or Active results; all 33 auxiliary/supplementary groups remain
Pending. Whole-paper certification remains false.

### Polynomial Fourier GitHub execution

The same verifier succeeded at exact proof commit
[`25dea299d18e2a423404488ac1a923fded0cde7b`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/25dea299d18e2a423404488ac1a923fded0cde7b),
whose tree is `0329196f131b11b8d416917ff417c4ceb90578b1`.

- [Successful run 43611293071, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43611293071).
- Verification job: `132496696818`; every step succeeded.
- Artifact: `14120945036`, 58,271 bytes, created `2026-11-14T15:44:27Z`.
- [Preserved CI report](certification/ci/run_43611293071_attempt_1.json), 492,952 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43611293071_attempt_1.zip).
- ZIP SHA-256: `e2e4750b08ac9687568d726fe155f7a409573c1b71254b1b6f9edd26190cede7`.
- CI report SHA-256: `482496c1212f5d366ebf1d54f8fd223bc58aa7cadf464582250931b60a6c060a`.

The downloaded ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, and both archived files are
byte-identical to the download and extracted member. The CI and local
reports agree exactly on all 18 verification-content fields: all 325 full
theorem records and their actual types and axiom dependencies, all four
registered-premise records, all 87 input hashes, all nine pinned dependency
revisions, the complete Lean export-inspection output, the Lean version,
and all verification flags and scope counts. The only differing fields are
`generated_at_utc` and `lake_build_output`.

Every recorded input hash also matched the files at that proof commit.
This preserved evidence covers the original 325-export scope and its eight
certified numbered results, before the diagonal milestone. The preserved
earlier runs below retain their original scopes; whole-paper certification
remains false.

### Exceptional-plane local execution

This preceding checkpoint contained 302 theorem exports across 59 project
Lean modules, four registered literature premises, 80 verification input
hashes, and 20 mapped source groups. Independent source reviews covered
the exact composite Bertini interface and every clause of Lemma 4.1(ii),
including the geometric witness, prime-field descent, uniform degree,
and final `D_p` construction. Together with the earlier reviewed part (i),
that completed Lemma 4.1.

The aggregate local verifier passed for all 59 modules, 302 theorem
exports, four registered literature premises and 80 input hashes. It
checked each module directly with strict settings, inspected declaration
kinds and actual types, verified the exact premise type hashes and allowed
axiom dependencies, and checked all nine pinned dependency revisions.
Every recorded input hash matched the files at that checked proof commit.
All 261 preceding theorem types and axiom dependencies were unchanged.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/afdaf2497bcd76fdff8b658efef8e28f0388f5b7/certification/verification_report.json)
records that completed execution. Its SHA-256 is
`36fe3c138da8345206a445c3968cf38c8e650916f8d7779fd7dbc11752a7b324`.

### Exceptional-plane GitHub execution

The independent GitHub verifier also passed for the exact proof commit
[afdaf2497bcd76fdff8b658efef8e28f0388f5b7](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/afdaf2497bcd76fdff8b658efef8e28f0388f5b7),
whose tree is `1bbf8bd0ddc4fb32d66871ed8424793cc21e0ffa`.

- [Successful run 43608132418, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43608132418).
- Verification job: `132487086734`; every step succeeded.
- Artifact: `14118739233`, 53,297 bytes.
- [Preserved CI report](certification/ci/run_43608132418_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43608132418_attempt_1.zip).
- ZIP SHA-256: `63320ecada162fd33fda88598056eac35ed8e093461d030711e9cdd7f64e304d`.
- Report SHA-256: `e33bff89ac7be8a07b7606b85d94d08d33613494995ce4c276a5239c8e2576e0`.

The ZIP digest matched the one advertised by GitHub. Its extracted report
matched the local report exactly on all 80 input hashes, 302 complete theorem
records, four literature-input records, nine dependency revisions and all
certification counts and flags. The only top-level differences were the
generation timestamp and build log. All 80 checked hashes also matched the
published proof files and source records at that checkpoint. That report
records seven Certified, one Partial, and 34 Pending numbered results.
The archived runs retain their original scopes.

### Bad-reduction, height, and quadratic-trace local execution

This preceding checkpoint contained 261 theorem exports across 50 project
Lean modules, 70 verification input hashes, 19 mapped source groups, and
three external Lean premises: Weil, Katz/Fulton, and Lang. Independent
source reviews covered the exact Lang interface, all of Lemma 4.1(i),
and completion of Lemma 5.9.

The full verifier passed on 13 November 2026 at 23:05 CST. It checked the frozen
manuscript and PDF, all 42 numbered statement identities, the dependency
ledger, pinned dependency checkouts, all 50 project modules, and the actual
types and axiom dependencies of all 261 registered theorem exports.
Every module was also checked directly with `warningAsError=true` and
`autoImplicit=false`.

The three literature declarations were separately inspected as axioms, and
their actual types match their reviewed type hashes. Of the theorem exports,
236 use only the standard foundations `propext`, `Classical.choice`, and
`Quot.sound`; seven additionally use Weil, eight Katz, eight Lang, and two
both Katz and Lang. Those last two are the complete quadratic-trace exports.
The two source components of the composite Katz premise remain separately
registered and validated.

All 70 input hashes matched the verified files at that proof commit, including ten correspondence
records. The full Lemma 4.1(i) export places the positive constants before
the form G. The final Lemma 5.9 types contain no separately assumed
finiteness or good-reduction condition. Source review found no missing
clause or strengthened hypothesis in these completed statements.

- [Local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/cc87de7c88dc32339bb59636ac0127a19bbdde76/certification/verification_report.json).
- Lean: official 4.24.0.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Manuscript SHA-256: `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

### Bad-reduction, height, and quadratic-trace GitHub execution

The same verifier passed at the exact proof commit
[cc87de7c88dc32339bb59636ac0127a19bbdde76](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/cc87de7c88dc32339bb59636ac0127a19bbdde76).

- [Successful run 43559876500, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43559876500).
- Verification job: 132340944839.
- Artifact: 14100255355.
- [Preserved CI report](certification/ci/run_43559876500_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43559876500_attempt_1.zip).
- ZIP SHA-256: `3ac9416897828dece4ccce6465aa58e0a2ceca5cdf29d4fe525277b4bbbf5ef5`.
- Report SHA-256: `bbab231f27d91a2218f6d6abe4df0e99afeaf49e5dfb2756a79b3b3e535e5a48`.

The original artifact was downloaded and its digest matched GitHub's recorded
SHA-256. The ZIP contains the verification report alone. All 70 input hashes
matched the files at that proof commit, including ten correspondence reviews.
All 261 theorem records, all three separately inspected literature-input
records, and all nine pinned dependency revisions matched the local report.
The CI report records six Certified, two Partial, and 34 Pending numbered
results, and leaves whole-paper certification false.

This preserved evidence covers the original 261-export scope at `cc87de7`.
The manuscript-name wording updates do not alter the frozen manuscript or
the original verification artifacts; their new file hashes belong to a later
verification report. The successful runs below retain their earlier scopes.

### Katz local execution

The Katz checkpoint covered 207 theorem exports across 38 project Lean
modules, 56 verification input hashes, 19 mapped source groups, and two
separately registered external Lean premises: the Weil input and the
composite Katz/Fulton spectral input.

The full verifier passed on 13 November 2026 at 22:39 CST. It checked the frozen
manuscript and PDF, all 42 statement identities, the dependency ledger,
pinned dependency checkouts, every project module, and all registered
declarations. Direct Lean execution used `warningAsError=true` and
`autoImplicit=false`.

All 207 proved exports were inspected as theorem declarations, and both
literature inputs were separately inspected as axioms with their reviewed
type hashes. Of the theorem exports, 192 use only the standard foundations
`propext`, `Classical.choice`, and `Quot.sound`; seven additionally use the
registered Weil input, and eight additionally use the composite Katz input.
No export uses both literature premises. The two source components of the
Katz input are separately recorded and validated.

All 56 input hashes matched the verified files at that checkpoint, including
eight correspondence records. Independent source reviews found no missing clause or strengthened
hypothesis in Lemma 2.7. At that checkpoint, the actual types of the
Lemma 5.9 wrappers retained their explicit finite-set argument, as recorded
in its then-Partial status.
The metadata checks also rejected a composite registration with an omitted
source component and one whose secondary source did not register the declaration.

- [Local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/ef786b7f270a017dfce7ae702f1b720ff1084ef2/certification/verification_report.json).
- Lean: official 4.24.0.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Manuscript SHA-256: `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

### Katz GitHub execution

The same verifier passed at the exact proof commit
[ef786b7f270a017dfce7ae702f1b720ff1084ef2](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/ef786b7f270a017dfce7ae702f1b720ff1084ef2).

- [Successful run 43557804300, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43557804300).
- Verification job: 132334510120.
- Artifact: 14098914113.
- [Preserved CI report](certification/ci/run_43557804300_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43557804300_attempt_1.zip).
- ZIP SHA-256: `90174464799304606926d69cafb5eac9cda02a72d1340d4178f6015a0f80d611`.
- Report SHA-256: `268626f13be0e8c998704cd0bc8da601b5cc8439a29009d580d5f08c2bf2c370`.

The original artifact was downloaded and its digest matched GitHub's recorded
SHA-256. The ZIP contains the verification report alone. All 56 input hashes
matched the local verified files at that checkpoint, including the eight
correspondence reviews.
All 207 theorem records, both separately inspected literature-input records,
and the pinned dependency revisions matched the local report. The CI report
records five Certified, two Partial, and 35 Pending numbered results; it
explicitly leaves whole-paper certification false.

The subsequent evidence commit changed only README, this checkpoint, and the
preserved CI JSON and ZIP. At that checkpoint, the Lean sources, verifier,
statement ledger, and correspondence records remained identical to the
checked proof commit.

The actual quadric geometry, coefficient calculation, finite-sum inequality,
and good-reduction arithmetic introduce no further external premises.
The Katz bound and quadratic-trace size exports used the spectral
input; they do not depend on the separate Weil estimate.

### Conic and plane-section local execution

The full verifier passed on 13 November 2026 at 21:50 CST. It checked the unchanged
frozen manuscript and PDF, all 42 numbered statement identities, the dependency
ledger, pinned dependency checkouts, all 31 local Lean modules, 162 registered
theorem exports, and the one separately registered literature premise. The
direct Lean checks use `warningAsError=true` and `autoImplicit=false`.

The 155 geometric, algebraic, and earlier theorem exports that do not apply
the Weil bound use only `propext`, `Classical.choice`, and `Quot.sound`.
Seven character-sum exports additionally use the exact registered declaration
`QuaternaryQuadraticForms.Trusted.weil_simple_roots`. Its actual type still
matches the reviewed type hash. Every registered proved export was inspected
as a theorem; the single literature input was inspected separately as an axiom.

All 47 recorded input hashes matched the checked files at that checkpoint, including the six
correspondence records. The final actual type of `conic_parametrization`
chooses the tuple before quantifying over extension fields. The final type of
`plane_section_bound` assumes the literal geometric matrix-rank condition
and constructs the parametrizations internally. Independent source review
found no missing clause or strengthened manuscript hypothesis.

- [Local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/0fccf5379e067d349cb0f14b6dc226bc8096033b/certification/verification_report.json).
- Lean: official 4.24.0.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Manuscript SHA-256: `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

### Conic and plane-section GitHub execution

The same verifier passed at the exact proof commit
[0fccf5379e067d349cb0f14b6dc226bc8096033b](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/0fccf5379e067d349cb0f14b6dc226bc8096033b).

- [Successful run 43553749446, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43553749446).
- Verification job: 132321811531.
- Artifact: 14096304719.
- [Preserved CI report](certification/ci/run_43553749446_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43553749446_attempt_1.zip).
- ZIP SHA-256: `e9ce332145032f0079ca8bc538cb72cf77b9d242d157d618d1d8db68546bfe0c`.
- Report SHA-256: `74cdccb5f5777b9d9460d7a560b47fc74661e1d35bed3784c80652e5a9a7001b`.

The original artifact was downloaded and its digest matched GitHub's recorded
SHA-256. The ZIP contains the verification report alone. All 47 input hashes
matched the local verified files at that checkpoint, including the six correspondence reviews.
All 162 theorem records, the separately inspected literature-input record,
and the pinned dependency revisions matched the local report. The CI report
records four Certified, two Partial, and 36 Pending numbered results; it
explicitly leaves whole-paper certification false.

The subsequent evidence commit changed only README, the checkpoint, and the
preserved CI JSON and ZIP. At that checkpoint the Lean sources, verifier,
statement ledger, and correspondence records remained identical to the
checked proof commit.


### Weil and projective-line local execution

The full verifier passed on 13 November 2026 at 21:29 CST. It checked the unchanged frozen
manuscript and PDF, all 42 numbered statement identities, the dependency
ledger, pinned dependency checkouts, all 16 local Lean modules, 68 registered
theorem exports, and the one separately registered literature premise.
The direct Lean checks use warningAsError=true and autoImplicit=false.

The 64 geometric, algebraic, and earlier theorem exports use only the
standard foundations propext, Classical.choice, and Quot.sound. Four
character-sum exports additionally use the exact registered declaration
QuaternaryQuadraticForms.Trusted.weil_simple_roots. Its actual type is
compared against the reviewed type hash, and the environment inspection
checks that it is an axiom while every proved export is a theorem.

The checker rejects unregistered axiom declarations, unexpected axiom
dependencies, altered premise types, and proof placeholders. Negative source
policy checks also rejected an additional axiom, an additional constant, a
missing or duplicated premise, and a proof placeholder. All four
correspondence records are included in the verification report's input hashes.

- Lean: official 4.24.0.
- mathlib: f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- Frozen manuscript: d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33.
- [Local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/450ff678b56b0a32a76b848278b53ba697958939/certification/verification_report.json).

### Weil and projective-line GitHub execution

The same verifier passed in GitHub Actions at the exact proof commit
[450ff678b56b0a32a76b848278b53ba697958939](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/450ff678b56b0a32a76b848278b53ba697958939).

- [Successful run 43551946447, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43551946447).
- Verification job: 132316195320.
- Artifact: 14096052644.
- [Preserved CI report](certification/ci/run_43551946447_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43551946447_attempt_1.zip).
- ZIP SHA-256: e12b55a4ff9e680d68950cb410628f89b3319b2268b9e86361396c92e96fe73a.
- Report SHA-256: ac477c5d4e3d1b48f242946e1228a83226e3690eaee1dbbc971f5ccebd48f8d5.

The downloaded artifact was inspected. All 30 recorded input hashes matched
the files at that checkpoint, including the four correspondence records.
All 68 theorem records and the separately inspected literature-input record
matched the local actual types and axiom dependencies. The CI report records two
Certified, two Partial, and 38 Pending numbered results, with one registered
external mathematical premise.

The later commit that preserved this evidence changed documentation and
evidence records only. At that checkpoint, the proof sources, checker,
status ledger, and correspondence records remained those of the checked
proof commit linked above.

### Quadratic-trace divisibility

The quadratic-trace divisibility checkpoint passed at proof commit
[ee274f6752d5a28e875919349821518b297e3115](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/ee274f6752d5a28e875919349821518b297e3115),
with [successful run 43550688913](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43550688913).
Its [report](certification/ci/run_43550688913_attempt_1.json) and
[original artifact](certification/ci/run_43550688913_attempt_1.zip) remain preserved.

### Fourier ray identity

The complete ray identity was checked at proof commit
[9c9840ed04c90a22af480eec1e1fe6eee168487b](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/9c9840ed04c90a22af480eec1e1fe6eee168487b),
with [successful run 43547207971](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43547207971).
Its [report](certification/ci/run_43547207971_attempt_1.json) and
[original artifact](certification/ci/run_43547207971_attempt_1.zip) remain preserved.
The initial algebra-only report is also preserved as
[run_43545694187_attempt_1.json](certification/ci/run_43545694187_attempt_1.json).

## Continuation status

This step stops after the dual-cone count and inner-modulus partial summation.
Acceptance is governed by the live ledger and focused execution record above.
The numbered inventory remains **27 Complete, 0 Partial, 0 Active, 15 Pending**;
the supplementary coverage is **7 Certified, 26 Pending**.

**The next target is the remaining assembly of Lemma 5.3**: the mixed-sum
factors, Poisson normalization, and dual-cone count must be combined for the
bounded on-cone contribution. Lemma 5.3 remains Pending. Proposition 5.1 and
absolute singular-integral convergence for weights whose support contains the
origin also remain Pending. The whole paper is not certified.

### Completed coefficient continuation

The increasing-modulus value `singularSeriesValue q A 0` is multiplied by the
original `C_q(0)/q^3`. The proof keeps this ordered limit at exponent zero.
The exact product combines `singularSeriesValue_zero_eq`, the source Fourier
prime product, squarefreeness, and an explicit bijection between their
prime-index sets. The nonsquare-determinant hypothesis is retained.

The local deductions give `|C_p(0)|<=2*K*p^2` without an assumption that
`D_p(0)=0`, and `|sigma_p^(-1)|<=2` at good primes. Their product gives
`|S_xi(q)|<=|S_F|*(4*K)^omega(q)/q`. The fixed-base epsilon estimate gives
the uniform `q^(-1+epsilon)` bound. The equality
`singularSeriesConstant M chi A = singularSeriesValue 1 A 0` proves that
the chosen constant depends only on the form, K, and epsilon, before every
admissible supplied character and level. All factors remain multiplicative
when `S_F=0`; no bad-prime density or zero Fourier value is divided out.
