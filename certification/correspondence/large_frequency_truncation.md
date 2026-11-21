# Lemma 5.2: the large-frequency clause

## Exact scope

This review covers only the first clause of Lemma 5.2: the terms with
Euclidean frequency norm greater than `U = sqrt(q)*B^eta` contribute `O(1)`
to the actual Poisson expression (5.4). The source is
`manuscript/quadratic_character_sums_github.tex`, with the statement at lines
2126–2130 and the large-frequency calculation at the start of its proof.
Its SHA-256 remains
`e3cd28b361ec143d043d4d9ced55939c234648f73f23a05377af4aaefa98b49a`.

Successful kernel execution completes this clause; Lemma 5.2 is **Partial**.
The bounded nonzero off-cone estimate `O((Bq)^(1+8*eta))` remains Pending.
No other numbered or auxiliary status is promoted.

The three supplied files are preserved byte-for-byte:

| Module | Lines | Role |
| --- | ---: | --- |
| [EuclideanFrequencyTail.lean](../../QuaternaryQuadraticForms/EuclideanFrequencyTail.lean) | 96 | Absolute Euclidean lattice tails |
| [PoissonFrequencyArithmetic.lean](../../QuaternaryQuadraticForms/PoissonFrequencyArithmetic.lean) | 108 | The actual mixed complete-sum bound and supporting identities |
| [PoissonFrequencyTail.lean](../../QuaternaryQuadraticForms/PoissonFrequencyTail.lean) | 199 | Strict cutoffs, normalization and the uniform large-frequency estimate |

The principal source endpoint is
`QuaternaryQuadraticForms.source_large_frequency_truncation`.
`DeltaIntegralBounds.largeFrequency` provides the estimate for a given
localized family, and `integerEuclidean_frequency_tail` proves its
summability input.

## Euclidean lattice tail and summability

For every natural `k >= 1` and real `U >= 1`, the proof establishes both
summability and the actual bound

```text
sum_{u in Z^4, norm(u) > U} norm(u)^(-k-4) <= 2592/U^k.
```

The norm is the Euclidean norm of the coordinatewise embedding of the
integer four-vector. A finite-set argument chooses its smallest radius
`M > U`. The points with radius at most `2*M` lie in a coordinate box with
at most `(6*M)^4` points, giving a contribution at most `1296/M^k`.
Induction bounds the remaining contribution by `2592/(2*M)^k`, which is
at most `1296/M^k` because `2^k >= 2`. Bounded finite sums of the
nonnegative terms then give genuine infinite summability.

The large-frequency integral term is dominated by that summable function
before its `tsum` is estimated. The proof does not rely on the value Lean
assigns to a nonsummable series. The cutoff remains strictly `norm(u) > U`.

## The original sums, integral and modulus cutoff

The arithmetic bound is for the literal `sourceMixedCompleteSum` formed
from the supplied prime functions. The composite weight has norm at most
one; additive characters have norm one. Counting the four residue
coordinates and the units gives `abs(S_{q,c}(u)) <= q^4*c^5`.

`sourceLargeFrequencyTerm` retains the factor `c^(-4)` and the actual
oscillatory integral at scale `c/Q` and frequency `u/sqrt(q)`. Applying the
existing rapid-decay estimate of Lemma 2.2 at order `k+4` and the lattice
tail gives, for each positive modulus,

```text
abs(sourceLargeFrequencyTerm)
  <= 2592*K*q^4*Q*(sqrt(q))^(k+4)/U^k.
```

`poissonModuliBelow R` represents exactly the positive integers `c < R`.
Its cardinality is at most `R` for `R >= 0`, including integral cutoff
values. Thus summing preserves the manuscript's strict cutoff `c < r0*Q`.

## Normalization and the uniform constant

The prefactor is the actual `c_Q*B^2/q^3`. From `B >= 9` and `q <= B`,
the proof obtains `Q = B/sqrt(q) >= 3`. The existing delta normalization
certificate then bounds `c_Q` by a constant `H+1`, uniformly in `Q`.

After the modulus sum, the bound is exactly

```text
(H+1)*r0*2592*K * (B^4*q^2 / B^(eta*k)).
```

Choose an integer `k > 6/eta`. Since `q <= B` and `B >= 1`, the quotient
is at most one. The resulting positive constant precedes `N`, the prime
functions, the modulus, `B`, and the individual weight. The source endpoint
obtains a common localization `delta` and cutoff `r0` from the existing
certified Lemma 2.2, before the exponent and individual pieces. The result
holds for every `eta > 0`, including the manuscript's narrower range.

## Supporting exports and status boundary

All eight public theorem exports in these files were reviewed. The
additional zero-frequency identities in `PoissonFrequencyArithmetic.lean`
retain the original source weights and sums, including the coprime case
`q = 1`. They are registered as supporting exports; Lemma 5.4 stays Pending.

No literature premise is added. Six exports use only the standard logical
foundations, one uses the existing delta-construction premise, and the
source-family endpoint uses the seven already registered analytic premises.
The original package records, source hashes and report identity are
preserved in [the extracted evidence](../local/large_frequency_package_evidence.json).

## Review and execution evidence

Independent source review found no required fatal, serious, moderate or
light correction in this first-clause batch.

The [focused GitHub run 44850308809](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/44850308809)
passed at proof commit [bc62790b3f58](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/bc62790b3f582b149d3fd8ab9a21f26d56f8f33c).
The three supplied modules built successfully and passed strict compilation;
all eight actual theorem types and axiom sets matched the supplied records.
The seven used literature-premise types and all nine pinned dependency
revisions also passed inspection. All 141 recorded proof/checker input hashes
match the integrated files, including the 134-module project import closure.
The [preserved execution report](../ci/large_frequency_run_44850308809_attempt_1.json) records the precise scope and
results. Its SHA-256 is
`1dea571ecdd1dc04476a17ab35d6aad0243e9ec076327b833dd5d7ffe0e57c1d`.
This focused execution covers only the first clause of Lemma 5.2 and its
supporting exports; the ordinary full-repository workflow remains an
additional regression check.

The focused check is reproducible with
`python3 scripts/verify_large_frequency.py` after fetching the pinned
dependencies and official mathlib cache. It checks exact supplied bytes,
the existing repository metadata rules, strict compilation, declaration
kinds, all eight actual theorem types and axiom sets, the used premise
types, and the dependency pins. The full repository workflow remains an
additional regression check.
