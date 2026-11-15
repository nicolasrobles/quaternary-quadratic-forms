# Source correspondence: Lemma 3.8

## Scope and frozen source

This review concerns every assertion of `lem:density`, Lemma 3.8:
the existence of the actual local counting limit at every prime, its
identification with an absolutely convergent complete-sum series, the
good-prime rational formula, and absolute convergence of the corrected
Euler product in `eq:SF`.

The source is
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
with frozen SHA-256
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

| Source location | Reviewed content |
| --- | --- |
| `eq:forms`, lines 157–167 | Symmetric nonsingular integral `A`, the actual form `F(x)=xᵀAx`, determinant `α`, bad-prime modulus `N_F=2|α|`, and the supplied character's Legendre values at good primes |
| `eq:singint`, lines 178–183 | The density defined by the limit of the normalized count of every zero modulo `p^k` |
| `eq:SF`, lines 184–188 | The product with factors `(1−χ(p)/p)σ_p`, multiplied by `L(1,χ)` |
| `eq:Sdef`, lines 1029–1039 | The actual complete sum `S_c(u)` over units and four-coordinate residue vectors |
| Lemma 3.2(ii), `eq:unram`, lines 1101–1104 | The checked good-prime-power evaluation of `S_(p^k)(u)` |
| Lemma 3.3, `eq:badbound`, lines 1156–1161 | The checked bound `|S_c(u)| ≤ 4|det A|^(1/2)c³` for every positive modulus |
| `lem:density`, `eq:densityseries`, `eq:sigmagood`, lines 1410–1420 | All four assertions being reviewed |
| Lines 1422–1433 | Actual zero counts, additive orthogonality, and the finite counting identity |
| Lines 1434–1444 | The absolute local series, the good-prime geometric series, and the corrected product |

The complete source endpoint is `source_local_density`. Its local
assertions are quantified over every prime, including two and all
primes dividing `N_F`. Its product uses the original supplied
Dirichlet character at every prime. No positivity or nonvanishing
hypothesis on a bad local density is imposed.

This milestone does not concern the restricted singular-series
identity or its tail estimate in Lemma 3.9, which begins at line 1446.
The value or analytic continuation of `L(1,χ)` is not a new premise
or conclusion of Lemma 3.8: the product assertion concerns precisely
the product appearing beside that fixed factor in `eq:SF`.

## Modules and public theorem exports

All declaration names below belong to the
`QuaternaryQuadraticForms` namespace. Every listed public theorem's
actual printed type and axiom list has been inspected. The verification
section distinguishes these completed source and targeted kernel
checks from aggregate execution evidence and exact-commit CI records.

| Module | Public theorem exports | Reviewed role |
| --- | ---: | --- |
| [LocalDensityDefinitions.lean](../../QuaternaryQuadraticForms/LocalDensityDefinitions.lean) | 0 | Literal finite zero counts, normalized real counts, complex complete-sum coefficients, and the counting-limit definition of the density |
| [PrimePowerScalarDecomposition.lean](../../QuaternaryQuadraticForms/PrimePowerScalarDecomposition.lean) | 1 | `sum_primePower_scalars`: an exact partition of all scalar residues into units and unique multiples of the prime |
| [LocalDensityGaussReduction.lean](../../QuaternaryQuadraticForms/LocalDensityGaussReduction.lean) | 2 | `integralQuadraticGaussSum_scaled_modulus`, `primePower_fullGauss_recurrence`: cancellation of a common scalar/modulus factor and the resulting full scalar-sum recurrence |
| [LocalDensityCounting.lean](../../QuaternaryQuadraticForms/LocalDensityCounting.lean) | 5 | `primePowerZeroCount_additive`, `normalizedPrimePowerZeroCount_eq_fullGauss`, `normalizedPrimePowerZeroCount_recurrence`, `normalizedPrimePowerZeroCount_zero`, `normalizedPrimePowerZeroCount_eq_sum`: the actual finite counting identity including exponent zero |
| [LocalDensitySummability.lean](../../QuaternaryQuadraticForms/LocalDensitySummability.lean) | 3 | `localDensityTerm_norm_le`, `summable_norm_localDensityTerm`, `summable_localDensityTerm`: the exact geometric majorant and absolute convergence at every prime |
| [LocalDensityConvergence.lean](../../QuaternaryQuadraticForms/LocalDensityConvergence.lean) | 4 | `localQuadraticDensity_eq_tsum_re`, `tendsto_normalizedPrimePowerZeroCount`, `hasSum_localDensityTerm`, `localQuadraticDensity_nonneg`: the real counting limit and its proved equality with the complex series |
| [LocalDensityGoodPrime.lean](../../QuaternaryQuadraticForms/LocalDensityGoodPrime.lean) | 5 | `localDensityTerm_zero`, `legendreSym_complex_norm_le_one`, `localDensity_goodPrime_ratio_norm_lt_one`, `localDensityTerm_goodPrime_succ`, `localDensityTerm_hasSum_goodPrime`: the actual coefficient evaluation and convergent geometric sum |
| [LocalDensityEulerProduct.lean](../../QuaternaryQuadraticForms/LocalDensityEulerProduct.lean) | 8 | `localQuadraticDensity_goodPrime`, `source_localQuadraticDensity_goodPrime`, `correctedLocalDensityFactor_goodPrime`, `correctedLocalDensityFactor_sub_one_norm_le`, `eventually_prime_not_dvd_quadraticBadPrimeModulus`, `summable_norm_correctedLocalDensityFactor_sub_one`, `multipliable_correctedLocalDensityFactor`, `multipliable_norm_correctedLocalDensityFactor`: original-character specialization and absolute convergence of the actual corrected product |
| [LocalDensityTheorem.lean](../../QuaternaryQuadraticForms/LocalDensityTheorem.lean) | 2 | `local_density`, `source_local_density`: the local assertions and the complete source-character statement |

These are thirty public theorem exports in nine modules. The four
definitions in `LocalDensityDefinitions.lean`, the corrected-factor
definition, and the private residue-digit equivalences are concrete
objects, not additional numbered results. Private helper statements
are proved within their modules and do not remain as hypotheses of
the final endpoints.

## Actual counts, sums, density, and character

| Manuscript object | Lean object and interpretation |
| --- | --- |
| `F(x)` | `integralQuadraticValue A x = dotProduct x (A.mulVec x)` |
| `N_F` | `quadraticBadPrimeModulus A = 2*A.det.natAbs` |
| `N_(p,k)` | `primePowerZeroCount p k A`, the cardinality of the filtered universe of `Fin 4 → ZMod (p^k)` on which the actual quadratic value reduces to zero |
| `p^(−3k)N_(p,k)` | `normalizedPrimePowerZeroCount p A k : ℝ` |
| `S_(p^k)(0)/p^(4k)` | `localDensityTerm p A k : ℂ`, using the existing `unweightedCompleteSum` at the zero integral frequency |
| `σ_p` | `localQuadraticDensity p A : ℝ`, defined by `limUnder Filter.atTop` of the actual normalized counting sequence |
| `χ(p)` | The original supplied `χ : DirichletCharacter ℂ M`, evaluated at `(p : ZMod M)` in the source endpoints |
| `(1−χ(p)/p)σ_p` | `correctedLocalDensityFactor M χ A p`, indexed by the actual subtype `Nat.Primes` |

The count is literally

```lean
(Finset.univ.filter (fun x : Fin 4 → ZMod (p ^ k) =>
  (integralQuadraticValue A (residueLift (p ^ k) x) :
    ZMod (p ^ k)) = 0)).card
```

Every residue vector is considered, including the origin. The
canonical integer lift is used only to evaluate the integral
polynomial; reducing that value modulo `p^k` is the actual congruence
`F(x)≡0`. Existing lift-congruence identities identify it with the
quadratic value for the reduced coefficient matrix. No smooth-locus,
primitive-vector, or projective count is substituted.

The complete sum retains the established unit group, residue
vectors, and positive standard additive character from `eq:Sdef`.
The density is defined from the real counting sequence, independently
of the complex series. Its convergence and the identification of its
value with the series are subsequent theorems; neither is built into
the definition.

For the source character the endpoints use precisely the explicit
good-prime value property from lines 165–167:

```lean
∀ (p : ℕ) [Fact p.Prime], ¬p ∣ quadraticBadPrimeModulus A →
  χ (p : ZMod M) = (legendreSym p A.det : ℂ)
```

The proof is valid for any actual Dirichlet character satisfying this
property. Thus the source's nonsquare determinant and primitivity
assumptions need not be reintroduced as extra local hypotheses. The
source character is supplied, as in the established Lemma 3.5 bridge;
this milestone does not redefine its primitive modulus or prove a
separate construction of the quadratic field character.

The good-prime property is never used to replace the character at a
bad prime. In particular, the corrected product is not defined using
a Jacobi coefficient at those exceptional primes.

## Finite counting identity

For a nonzero natural base `p`, additive orthogonality gives

$$
p^kN_{p,k}
=\sum_{a\bmod p^k}\sum_{x\bmod p^k}e_{p^k}(aF(x)).
$$

`primePowerZeroCount_additive` proves this exact identity by applying
primitivity of `ZMod.stdAddChar` at the composite modulus `p^k`,
interchanging the two finite sums, and identifying the resulting
zero indicator with the defining filter of `primePowerZeroCount`.
The identity does not require a good prime or a nonsingular reduced
matrix. It also covers modulus one.

The source sorts all scalar residues by their exact valuations.
The formal proof implements the same finite decomposition one power
at a time. For prime `p`, `sum_primePower_scalars` proves

$$
\sum_{a\bmod p^{k+1}}f(a)
=\sum_{a\bmod p^{k+1}}^{*}f(a)
 +\sum_{b\bmod p^k}f(pb).
$$

This is an identity for an arbitrary complex-valued function on the
actual scalar residue ring. The proof constructs residue digits
`r+p s`, with `r mod p` and `s mod p^k`, using the existing actual
residue-digit equivalence. The condition that the resulting scalar
is a unit is equivalent to the first digit being a unit modulo `p`.
Since `p` is prime, every nonzero first digit is a unit, and the zero
first digit gives exactly the displayed unique multiple `pb`.
No arbitrary representatives or assumed fibre cardinalities remain.

For positive `m,n`,
`integralQuadraticGaussSum_scaled_modulus` proves

$$
\sum_{x\bmod mn}e_{mn}(naF(x))
=n^4\sum_{y\bmod m}e_m(aF(y)).
$$

The established standard-character identity cancels the common
factor `n` from the scalar and modulus. The actual four-coordinate
residue digits `x=y+mz` leave the reduced quadratic value modulo
`m` unchanged. There are exactly `n^4` choices of `z`. This argument
does not require coprimality of `m,n`, symmetry of `A`, or oddness of
either modulus.

Writing the full scalar sum at modulus `p^k` as `T_k`, these two
identities give

$$
T_{k+1}=S_{p^{k+1}}(0)+p^4T_k.
$$

After division by `p^(4(k+1))` and the proved orthogonality identity,
the recurrence becomes

$$
p^{-3(k+1)}N_{p,k+1}
=p^{-3k}N_{p,k}+\frac{S_{p^{k+1}}(0)}{p^{4(k+1)}}.
$$

At exponent zero there is one vector modulo one, the congruence is
automatic, and the normalized count equals one. The previously
proved actual modulus-one complete sum is also one. Induction yields
`normalizedPrimePowerZeroCount_eq_sum`:

$$
\bigl(\operatorname{normalizedPrimePowerZeroCount}(p,A,k):\mathbb C\bigr)
=\sum_{j=0}^{k}\operatorname{localDensityTerm}(p,A,j).
$$

The Lean cutoff is `Finset.range (k+1)`, so both the zero term and the
terminal exponent are present. This recurrence proof is equivalent
to the source's exact-valuation grouping, and establishes the same
finite equality before any convergence argument.

## Absolute convergence and the real counting limit

The existing complete Lemma 3.3 supplies the actual bound

$$
|S_{p^k}(0)|\le4\sqrt{|\det A|}\,p^{3k}.
$$

`localDensityTerm_norm_le` divides by the exact fourth-power
normalization and proves, including `k=0`,

$$
\left\|\operatorname{localDensityTerm}(p,A,k)\right\|
\le4\sqrt{|\det A|}\left(\frac1p\right)^k.
$$

The majorant theorem itself only needs `p≠0`. To deduce summability,
primality gives `p≥2`, hence `0≤1/p<1`. The geometric series is
summable, so `summable_norm_localDensityTerm` proves absolute
convergence at every prime under symmetry and `det A≠0`.
`summable_localDensityTerm` supplies ordinary complex summability.
No good-reduction assumption occurs in these endpoints.

The finite counting identity identifies the complex coercion of
each real normalized count with the corresponding partial sum.
The natural partial-sum convergence theorem, composed with the
shift `k↦k+1`, therefore gives a complex limit equal to the complete
series. Applying the continuous real-part map gives a limit of the
actual real counting sequence. The defining `limUnder` is then
identified with this proved limit, yielding
`tendsto_normalizedPrimePowerZeroCount`.

Finally, continuity of the real-to-complex embedding and uniqueness
of the complex limit show that the entire complex sum, not merely
its real part, equals the coerced real density:

```lean
HasSum (localDensityTerm p A) (localQuadraticDensity p A : ℂ)
```

Thus reality of the series is proved from the actual counting
sequence. There is no assumption that its imaginary part vanishes,
and no projection of an unrelated complex value is used as the
source density. `localQuadraticDensity_nonneg` also derives
nonnegativity from the nonnegative finite counts. It does not
assert strict positivity or provide a hypothesis used to divide by
a possibly vanishing local density.

## The good-prime formula

At `p∤N_F` and every positive exponent, the existing complete
prime-power evaluation and the exact Ramanujan value at zero give

$$
S_{p^k}(0)=\chi(p)^k p^{2k}\varphi(p^k).
$$

`localDensityTerm_goodPrime_succ` uses the actual totient formula
`φ(p^(k+1))=p^k(p−1)` to obtain

$$
\operatorname{localDensityTerm}(p,A,k+1)
=\left(1-\frac1p\right)
 \left(\frac{(\det A/p)}p\right)^{k+1}.
$$

Only nonzero powers of `p` are cancelled in this algebra. No
character value or local density is divided out. The modulus-one
term remains the separately established value one.

The actual Legendre coefficient, viewed in the complex numbers,
has norm at most one. For every prime this proves

$$
\left\|\frac{(\det A/p)}p\right\|<1.
$$

Consequently the geometric series converges and its denominator
`1−(det A/p)/p` is nonzero. The exact summation gives

$$
1+\left(1-\frac1p\right)
 \sum_{k\ge1}\frac{(\det A/p)^k}{p^k}
=\frac{1-(\det A/p)p^{-2}}{1-(\det A/p)p^{-1}}.
$$

`localDensityTerm_hasSum_goodPrime` is a `HasSum` statement about
the existing complete-sum coefficients themselves. Uniqueness with
`hasSum_localDensityTerm` then identifies the rational expression
with the actual counting density. Substitution of the source's
given Legendre value at that good prime yields
`source_localQuadraticDensity_goodPrime`, with the original `χ` in
both numerator and denominator.

## Absolute convergence of the corrected product

The factor used throughout this part is literally

$$
E_p=\left(1-\frac{\chi(p)}p\right)\sigma_p,
$$

where `σ_p` is the actual real counting density and `χ` is the
original supplied character. All prime indices are present.
At a good prime the proved nonzero geometric denominator cancels,
giving

$$
E_p=1-\frac{\chi(p)}{p^2},\qquad
|E_p-1|\le\frac1{p^2}.
$$

The prime-restricted comparison series is summable because it is
the restriction of the convergent natural-number series
`∑ n≥1 1/n²`. The zero natural term in Lean's totalized expression
is zero and does not affect that comparison; the prime subtype
contains only primes at least two.

The exceptional primes are handled by their actual arithmetic
support. Nonsingularity proves `N_F≠0`, so every prime dividing
`N_F` belongs to its finite `primeFactors` set.
`eventually_prime_not_dvd_quadraticBadPrimeModulus` establishes the
good-prime condition in the cofinite filter on `Nat.Primes`.
The eventual comparison with `p⁻²` therefore proves

```lean
Summable (fun p : Nat.Primes =>
  ‖correctedLocalDensityFactor M χ A p - 1‖)
```

for the original factors at every prime. This explicit summability
of absolute deviations is the absolute-convergence certificate.
It is stronger information than merely naming a totalized infinite
product or exhibiting `Multipliable` in the presence of a zero
factor.

The proved complete-normed-ring infinite-product theorem applies to
`1+(E_p−1)`, yielding `multipliable_correctedLocalDensityFactor`.
Continuity of the norm gives the additional explicit endpoint
`multipliable_norm_correctedLocalDensityFactor`. No nonvanishing
assumption on any exceptional factor is used. In particular, if a
bad density vanishes, the full product may be zero while the
summability of deviations still certifies the convergent tail.

No assertion about absolute convergence of the uncorrected product
`∏p σ_p` is made. The character correction is part of the source
definition and of every product endpoint.

## Complete endpoint and boundary review

`source_local_density` combines, in one source-character theorem:

1. Convergence of the normalized real zero counts to the actual
   local density for every prime.
2. Summability of the norms of the literal local complete-sum
   coefficients and `HasSum` equal to that real density in `ℂ`.
3. The exact rational density formula at every prime outside the
   actual `N_F`.
4. Summability of the norms of the corrected-factor deviations,
   convergence of the corrected product, and convergence of the
   product of its norms, with every bad factor retained.

The following boundary cases are covered by the inspected statements
and checked deductions:

| Boundary | Reviewed treatment |
| --- | --- |
| `k=0`, modulus one | One actual residue vector, normalized count one, actual `S_1(0)=1`, and cutoff `range(k+1)` |
| `p=2` | Included in scalar decomposition, finite counts, the uniform bound, and all-prime convergence; never excluded from the product |
| Primes dividing `det A` | Included in actual counts and local absolute convergence; retained as finitely many original corrected factors |
| Vanishing bad density | Allowed without division or a nonzero hypothesis; absolute deviations remain summable |
| Real versus complex values | Real counting limit and full complex `HasSum` are identified by continuity and uniqueness of limits |
| Good-prime denominator | Nonvanishing is deduced from a strictly subunit geometric ratio |
| Original source character | The supplied character is retained at all primes; good-prime agreement is used only where it is stated in the source |
| Source standing hypotheses | Symmetry and nonsingularity are retained; removing unused nonsquare/primitivity assumptions strengthens this local theorem |

## Dependencies, trust, and verification status

The finite counting identity, the convergence estimates, the
reality argument, the rational formula, and the product argument
are internal deductions. They use the established complete-sum
definitions, residue-digit and character identities, and the
previously checked Lemmas 3.2 and 3.3. Standard mathlib geometric
series, continuity, `p`-series, and infinite-product theorems supply
the analytic background. No new external literature premise is
introduced, and no internal assertion of Lemma 3.8 is postulated.

All nine new modules have passed targeted strict compilation with
official Lean 4.24.0, `warningAsError=true`, and
`autoImplicit=false`. The final `source_local_density` assembly has
compiled successfully. The official toolchain release archive was
verified against its published SHA-256, and all nine dependency
revisions match the committed manifest.

A unified inspection of all thirty public theorem exports completed
successfully. The independent review read each actual printed type
and axiom list, matched every printed type to its parsed inspection
record, matched every recorded Lean source hash to the current file,
and checked that the thirty inspected names are exactly the public
theorem declarations in these nine modules. The literal counting
and density definitions also remain identical to the definitions
reviewed against the source.

Every new theorem has exactly the foundational axiom dependencies

```text
Classical.choice
Quot.sound
propext
```

No new theorem depends on a registered literature premise, an
unregistered axiom, or a proof placeholder. There is no change to
the repository's four separately registered literature premises.

The actual printed type of `source_local_density` contains only the
original matrix and supplied character, symmetry, nonsingularity,
and the source's stated Legendre values at good primes. Its
conclusions quantify over every prime and contain every local and
product assertion described above. No helper evaluation, finite
counting identity, local-density existence, summability,
nonvanishing bad factor, or product-convergence assumption survives
as an endpoint hypothesis. In particular, the finite counting and
convergence deductions have been discharged by the checked proof,
rather than placed behind the source-character wrapper.

These completed kernel, actual-type, axiom, and independent source
reviews establish the full source-relative scope of Lemma 3.8.
The subsequent aggregate verifier checks the frozen integration of
this scope with the existing repository. Its exact outcomes, the
checked GitHub commit, and any successful CI run are separate
execution evidence recorded in
[verification_report.json](../verification_report.json),
[README.md](../../README.md), and [CHECKPOINT.md](../../CHECKPOINT.md).
This correspondence record does not assert an aggregate or CI
outcome merely from the successful targeted checks. Those execution
records can be updated after the aggregate inputs, including this
source review, have been frozen.

The repository's live status ledger, readable inventory, and
execution checkpoint remain authoritative for the current
certification state. This record concerns only Lemma 3.8; it does
not certify Lemma 3.9 or the whole paper.
