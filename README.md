# Character sums over zeros of quaternary quadratic forms

Source-relative Lean verification of the paper by Hemjyoti Nath, Nicolas Robles,
and Alexandru Zaharescu.

The mathematical source is the audited frozen manuscript
[quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).
The associated [34-page PDF](manuscript/quadratic_character_sums_github.pdf) is
included. The source SHA-256 is

    d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33

## Current status

**Complete: 26 · Partial: 0 · Active: 0 · Pending: 16** — 42 numbered results.

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

### Current Lemma 5.1 verification

<!-- BEGIN LEMMA_5_1_VERIFICATION -->

The targeted strict build and inspection of all 45 new theorem declarations
have passed. Their actual types and axiom sets match the source review;
the new Poisson premise also matches its preregistered complete type hash.
Full local aggregate verification and exact-commit GitHub verification are
the remaining execution gates. Their results, exact proof commit, report
hashes, and comparison will be recorded here. Earlier evidence retains
its checked commit and historical scope.

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

**Lemma 2.5 and Corollary 2.6 are Certified relative to the accepted literature
inputs.** Lemma 2.5 is matched to the exact cited univariate Weil estimate.
Corollary 2.6 is proved for the actual projective-line character sum, including
the chart decomposition, polynomial dehomogenization, degree calculation,
distinct-root condition, and contribution at infinity.

**Lemmas 4.2 and 4.3 are Certified.** Lemma 4.2 constructs one tuple of binary quadratic forms over the
prime field and proves that its coefficient extensions parametrize the actual
conic over every extension field, with independent formal partial derivatives.
Lemma 4.3 deduces the simple-root condition from the manuscript's geometric
rank-three hypothesis and proves the bound for the actual projective section
sum. No restriction that the characteristic be prime to the degree is added.

**Lemma 2.7 is Certified.**
The exact quadric trace bound follows from the registered general Katz/Fulton
spectral interface, with the quadric geometry, coefficient calculation, and
scalar estimate proved internally. The full local verifier and the same
GitHub Actions verifier both passed at the preceding Katz checkpoint.

**Lemma 5.9 is Certified.** Characteristic-zero smoothness supplies a
nonzero integer divisible by every actual bad prime, so the defining
bad-prime set is finite. The final theorem uses the literal `p ∤ N_G`
hypothesis and proves that the projective trace is an integer divisible by
`p`, with absolute value at most `4p`. Finiteness and good reduction are
deduced inside this theorem.

**Lemma 4.1 is Certified.** Part (i) gives `N_G ≤ K H_G^C`, with
`C,K` fixed before the form `G`. Part (ii) constructs the nonzero polynomial
`D_p`, proves `D_p(0)=0`, and bounds its degree by a constant chosen before
both `G` and `p`. Nonvanishing of `D_p(u)` implies the dual-form condition
and the actual geometric rank-three transversality condition.

**Lemma 4.4 is Certified.** The actual polynomial character weight vanishes
at zero, has norm at most one, and is invariant under nonzero scalar
multiplication. The full pointwise bound
`|C_p(u)| ≤ 2n²(p^(3/2) + p² 1_{D_p(u)=0})` and exact zero-frequency
identity `C_p(0) = (p−1)a` are proved under the literal manuscript
hypotheses. The final uniform theorem chooses the degree bound before
`G,p` and the exceptional polynomial before the character. Its section
count includes tangent and singular sections. Theorems 1.1 and 1.4 remain
Pending.

**Lemma 4.5 is Certified.** For the actual diagonal forms, the source's
nonzero coefficient product and six nonzero pair determinants imply
characteristic-zero smoothness. At every prime outside `N_F`, geometric
bad reduction is equivalent to divisibility of the literal product `M`.
The actual bad-prime set is finite directly from `M ≠ 0`, and the existing
modulus equals `rad(|2αM|)`, including signs and shared prime divisors.
This proof uses no literature premise.

**Lemma 4.6 is Certified relative to the accepted Weil input.** For the
actual integral diagonal data and the literal condition `p ∤ 2αM`, the
exact Fourier formula includes every regular and singular pencil member.
It gives the integer trace identity `a_p(G) = p ∑ᵢ χ_p(κ_i)` and the
bound `|C_p(u)| ≤ 2p^(3/2)+4p` under the literal condition
`p ∤ F*(u)u₁u₂u₃u₄`. The exact formula and trace use only the standard
Lean foundations; the bound additionally uses the existing Weil premise.
All lemmas in Section 4 are now complete. Theorem 1.3 remains Pending:
its global asymptotic conclusion is not yet proved.

**Lemma 3.1 is Certified.** The actual mixed complete sum has both the
source CRT factorization and unit-frequency invariance under the literal
integer gcd condition. Its prime-product weights and all choices of
integer representatives are justified internally. The final source
wrapper accepts functions only at primes not dividing `N`. The proof
includes modulus one and permits shared prime factors between `q` and
`c`. The identities `𝒮_{1,c}=S_c`, `𝒮_{q,1}=C_q`, the prime-factor
formula for squarefree `C_q`, multiplicativity of `S_c`, and the exact
bridge to the earlier prime Fourier sum are also proved. This branch
uses no literature premise.

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

**Lemma 3.8 is Certified.** For every prime, the actual normalized
zero counts modulo `p^k` converge to a real local density, and the
literal series `Σ_(k≥0) S_(p^k)(0)/p^(4k)` converges absolutely to
that density. The finite counting identity includes exponent zero,
the prime two, and all bad primes. At `p ∤ N_F`, the density is
`(1−χ(p)/p²)/(1−χ(p)/p)`, with its denominator proved nonzero.
The corrected product `∏_p (1−χ(p)/p)σ_p` converges absolutely:
the norms of its factors minus one are summable. The original supplied
character and the actual density remain in every bad-prime factor,
including a factor that vanishes. No literature premise is added or used.

**Lemma 3.9 is Certified.** The actual restricted series converges in
increasing modulus order and equals the original-character singular-series
constant times the reciprocal good densities at primes dividing `q`.
Its literal real-cutoff tail satisfies `C_(F,epsilon) q^epsilon X^(-1+epsilon)`.
The final theorem chooses the positive constant before the supplied
character data, `q`, and `X`. The boundary uses the analytic `LFunction`
at one and a finite corrected Euler comparison. Original bad-prime
character values and possibly zero bad densities are retained.
No literature premise is added or used.

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

The current scope covers 1,087 theorem exports across 247 Lean modules,
11 separately registered external Lean premises, and 21 mapped source groups.
Five auxiliary/supplementary groups are Certified and 28 remain Pending.
This repository does not yet provide a certificate for the whole paper.

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

### Earlier Lemma 3.9 verification

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

### Earlier Lemma 3.8 verification

<!-- BEGIN LEMMA_3_8_VERIFICATION -->

The Lemma 3.8 milestone adds 30 public theorem exports in nine new
modules and one correspondence review. The complete aggregate scope
contains 205 inspected inputs. All nine modules passed strict
compilation under official Lean 4.24.0 with the pinned mathlib revision,
using `warningAsError=true` and `autoImplicit=false`.
The final `LocalDensityTheorem` target build passed with 3,144 jobs.

The unified inspection of all 30 actual theorem types and axiom lists
passed. Every new export uses exactly `Classical.choice`, `Quot.sound`,
and `propext`; none uses a literature premise. Independent source
review checked all four clauses, the actual real counting limit,
the complex series equality, the good-prime denominator, the original
character at bad primes, and summability of the corrected-factor
deviations. The complete
[source correspondence review](certification/correspondence/local_density.md)
records these checks and the boundary cases.

**The full local aggregate verifier passed for all 707 theorem
exports, 174 project modules, and 205 inspected inputs.** The resumed
execution checked the full build, each module with strict settings,
all actual declaration types and axiom dependencies, the frozen source,
and all nine pinned dependency revisions. The 677 earlier theorem
records and four literature-input records are unchanged; the 30 new
exports match their independent actual-type and source reviews.

- [Local report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/eac4b4c9e82470cf142ecd2a4290cfa35a44bf35/certification/verification_report.json).
- Report SHA-256: `0712a8eec668f9f44c87b1c318252ee424004af18f4f50d7bbbbbcc2b2659a56`.
- Current numbered inventory: 18 Certified, 0 Partial, 0 Active,
  and 24 Pending; all 33 auxiliary groups remain Pending.

**Independent GitHub verification passed for the exact published
proof commit [eac4b4c9e824](https://github.com/nicolasrobles/quaternary-quadratic-forms/commit/eac4b4c9e82470cf142ecd2a4290cfa35a44bf35).**
[Run 43725792541, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43725792541) completed successfully,
and every verification-job step succeeded.

- [Preserved CI report](certification/ci/run_43725792541_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43725792541_attempt_1.zip).
- Verification job: `132847314315`; artifact: `14166432952`.
- ZIP SHA-256: `05f9416df22887b06fff84ab49d4a429569f35e8052f6775da1144c27f10cb2a`.
- CI report SHA-256: `ff2b840c83a4604dbb1168a488a71091f8f0b403adeb5defdd82eac7ccaf530a`.

The artifact digest matches GitHub's recorded SHA-256. Independent
comparison matched the local and CI reports on all 18 verification-content
fields, including all 707 complete theorem records, all 205 input hashes,
the four literature-premise records, and nine dependency revisions.
All inspected inputs also match the files at the published proof commit.
The generation timestamp and build log are execution-specific fields.
The [execution checkpoint](CHECKPOINT.md) records the complete evidence.
Earlier reports below retain their historical scopes.

<!-- END LEMMA_3_8_VERIFICATION -->

### Earlier Lemma 3.7 verification

The preceding Lemma 3.7 scope covered 677 theorem exports across 165 Lean modules,
four unchanged separately registered external Lean premises, and 20 mapped
source groups. All 33 auxiliary/supplementary groups remain Pending.
This repository does not yet provide a certificate for the whole paper.

The Lemma 3.7 milestone adds 40 public theorem exports in fourteen new
modules and one correspondence review, with 195 recorded aggregate
input hashes. All fourteen modules passed strict compilation under
official Lean 4.24.0 with the pinned mathlib revision. The final
source-theorem target build passed with 3,151 jobs. The unified
inspection of all 40 actual theorem types and axiom lists passed:
39 exports use exactly `Classical.choice`, `Quot.sound`, and
`propext`; `goodQuadraticChar_coprime_four_iff` uses only `propext`.
No new export uses a literature premise. The
[source correspondence review](certification/correspondence/cone_modulus_bound.md)
records the complete statement, the derived character cancellation,
the actual order of summation, and uniformity of the final constant.

**The full local aggregate verifier passed for all 677 theorem
exports and 165 project Lean modules.** All 195 input hashes
match the checked files. The independent comparison preserved all
637 preceding complete theorem records and all 637 earlier support
records, including actual types, axiom lists, source hashes, and scopes.
All 40 new full types and axiom lists match the prior unified
inspection. Of these, 39 use exactly `Classical.choice`, `Quot.sound`,
and `propext`; `goodQuadraticChar_coprime_four_iff` uses only `propext`.
No new export uses a literature premise.

The four registered premise records and nine pinned dependency
revisions are unchanged. All 35 frozen changed-file hashes were
preserved through verification, including the workflow, which is
outside the report's 195 input hashes. The frozen manuscript and
PDF remain unchanged. The actual-type audit checked the source
endpoint's uniform constant order, nonsquare determinant, literal
integral dual-cone condition, real cutoff, exact gcd restriction, and
norm outside the actual complex sum.

The [local verification report at proof commit 5918e83](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/5918e83d0705f4c0ab3b24a3324da18b0ab5e027/certification/verification_report.json)
contains 996,216 bytes and has SHA-256
`17b3f004491f1a6cd601960232f86e467de2bece9d8df6531207a93722b6b4a5`.
It records 17 Certified, zero Partial or Active, and 25 Pending
numbered results; all 33 auxiliary/supplementary groups remain Pending.

**The local and GitHub verifiers passed for the complete 677-export
scope.** [GitHub Actions run 43680979628, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43680979628)
succeeded at [proof commit 5918e83](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/5918e83d0705f4c0ab3b24a3324da18b0ab5e027),
with verification job `132711319031`. Its artifact `14148294897`
is preserved as the [original ZIP](certification/ci/run_43680979628_attempt_1.zip) and
[downloaded report](certification/ci/run_43680979628_attempt_1.json).
The ZIP contains 118,804 bytes and has SHA-256
`df9534e5c6360fd3032ad5a82d8379362785cfb2c4d1c29c8551055b5d287424`;
the report contains 1,008,362 bytes and has SHA-256
`9a0621958cc3ad13be370a60dfa571ba777f0d7121160dba0d1346313fed3e0a`.

The ZIP digest matches GitHub's advertised artifact digest, and its
sole member is byte-identical to both independently inspected JSON
copies and the archived report. The root and agent comparisons agree
on all 18 verification-content fields: 677 complete theorem records,
four premise records, 195 input hashes, nine dependency revisions,
and the complete Lean inspection output. Only `generated_at_utc` and `lake_build_output` differ.

At that checkpoint all 195 hashes matched its inspected files and the exact proof
tree `cf6ecf868ee9642f9d9f165091e1ef35152d9fff`. All 33 frozen nondocument paths, including
the workflow, were checked against that proof tree. That accepted
local report has 996,216 bytes, with its
SHA-256 recorded above. Of the 40 new exports, 39 use exactly
`Classical.choice`, `Quot.sound`, and `propext`;
`goodQuadraticChar_coprime_four_iff` uses only `propext`.
No new export uses a literature premise.
The [execution checkpoint](CHECKPOINT.md) records the proof, run, job,
artifact, timestamps, and complete 677-export scope. Earlier evidence
below retains its historical scope.

This historical Lemma 3.7 evidence does not cover the new 707-export Lemma 3.8 milestone.

### Earlier Lemma 3.6 verification

The preceding Lemma 3.6 scope covered 637 theorem exports across 151 Lean modules,
four unchanged separately registered external Lean premises, and 20 mapped
source groups. All 33 auxiliary/supplementary groups remain Pending.
This repository does not yet provide a certificate for the whole paper.

The Lemma 3.6 milestone adds 39 public theorem exports in twelve new
modules and one correspondence review, with 180 recorded aggregate
input hashes. The twelve modules passed strict compilation, and the
final source-theorem target build passed with 3,158 jobs. The unified
inspection of all 39 actual theorem types and axiom lists passed;
every new dependency is a standard logical foundation. The
[source correspondence review](certification/correspondence/generic_modulus_bound.md)
records the precise statement, uniformity, and stronger intermediate bound.

**The full local aggregate verifier passed for all 637 theorem
exports and 151 project Lean modules.** All 180 input hashes
match the checked files. The independent comparison preserved all
598 preceding complete theorem records and all 598 earlier support
records, including actual types, axiom lists, source hashes, and scopes.
All 39 new full types and axiom lists match the prior unified
inspection; every new export uses exactly `Classical.choice`,
`Quot.sound`, and `propext`. No new export uses a literature premise.

The four registered premise records and nine pinned dependency
revisions are unchanged. All 33 frozen changed-file hashes were
preserved through verification, including the workflow, which is
outside the report's 180 input hashes. The frozen manuscript and
PDF remain unchanged. The independent audit also checked the actual
source endpoint's quantifier order, real cutoff, literal gcd set,
constrained Fourier factor, and exact divisibility indicator.

The [local verification report at proof commit 8acdea4](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/8acdea4a607ce8c59e198373bf2d72daa9a62525/certification/verification_report.json)
contains 942,183 bytes and has SHA-256
`ae070fa70d8f1f02efa7c5e2ee0496d396c7fded6c65fa66ec5946b36d3d90de`.
It records 16 Certified, zero Partial or Active, and 26 Pending
numbered results; all 33 auxiliary/supplementary groups remain Pending.

**The local and GitHub verifiers passed for the complete 637-export
scope.** [GitHub Actions run 43674573868, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43674573868)
succeeded at [proof commit 8acdea4](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/8acdea4a607ce8c59e198373bf2d72daa9a62525),
with verification job `132691791438`. Its artifact `14145627876`
is preserved as the [original ZIP](certification/ci/run_43674573868_attempt_1.zip) and
[downloaded report](certification/ci/run_43674573868_attempt_1.json).
The ZIP contains 111,239 bytes and has SHA-256
`64f3c79c1818b9a9518966e47c336f2c2e6339a82b7dbc8961faa7d55ce1dcff`;
the report contains 953,313 bytes and has SHA-256
`147b132a851d2f4601f1cafc9d7a6b9d65be7bc4d665959512c10b1c2912a61f`.

The ZIP digest matches GitHub's advertised artifact digest, and its
sole member is byte-identical to both independently inspected JSON
copies and the archived report. The root and agent comparisons agree
on all 18 verification-content fields: 637 complete theorem records,
four premise records, 180 input hashes, nine dependency revisions,
and the complete Lean inspection output. Only `generated_at_utc` and `lake_build_output` differ.

At that checkpoint all 180 hashes matched its inspected files and the exact proof
tree `758abd225eb380a9fd88b7c11ab3097654ff4f46`. All 31 frozen nondocument paths, including the
workflow, were checked against that proof tree. That accepted
local report has 942,183 bytes, with its
SHA-256 recorded above. All 39 new exports retain exactly the standard
logical foundations and use no literature premise.
The [execution checkpoint](CHECKPOINT.md) records the proof, run, job,
artifact, timestamps, and complete 637-export scope. Earlier evidence
below retains its historical scope.

This historical Lemma 3.6 evidence does not cover the new 677-export Lemma 3.7 milestone.

### Earlier Lemma 3.5 verification

The preceding Lemma 3.5 scope covered 598 theorem exports across 139 Lean modules,
four unchanged separately registered external Lean premises, and 20 mapped
source groups. All 33 auxiliary/supplementary groups remain Pending.
This repository does not yet provide a certificate for the whole paper.

The Lemma 3.5 milestone adds 27 public theorem exports in eleven new
modules, with 167 recorded input hashes including the new correspondence
review. Strict targeted compilation and the root library build passed
under the pinned settings (3,180 build jobs).

**The full local aggregate verifier passed for all 598 theorem exports
and 139 Lean modules.** All 167 input hashes match the checked files.
All 571 preceding complete theorem records remain identical, including
their actual types, axiom lists, Lean source hashes, and scopes. All
27 new actual types and axiom lists match their prior inspections:
26 exports use exactly `Classical.choice`, `Quot.sound`, and `propext`,
and `gcd_mul_blocks_coprime` uses only `propext`. No new export uses a
literature premise. The four registered literature premise records
and nine pinned dependency revisions are unchanged. All 32 frozen
changed-file hashes were preserved through verification, and the
frozen manuscript and PDF remain unchanged.

The [local verification report at proof commit 5d052df](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/5d052dfa49810e4456dfb6de6e30577493658496/certification/verification_report.json)
contains 879,086 bytes and has SHA-256
`307a164465319d2b0009cc2f3210c6674fbd9783aff81f39c883b55218b3bdeb`.
It records 15 Certified, zero Partial or Active, and 27 Pending numbered
results; all 33 auxiliary/supplementary groups remain Pending.

**The local and GitHub verifiers passed for the complete 598-export
scope.** [GitHub Actions run 43648807603, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43648807603)
succeeded at [proof commit 5d052df](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/5d052dfa49810e4456dfb6de6e30577493658496),
with verification job `132612448839`. Its artifact `14134999045`
is preserved as the [original ZIP](certification/ci/run_43648807603_attempt_1.zip)
and [downloaded report](certification/ci/run_43648807603_attempt_1.json).
The ZIP contains 103,724 bytes and has SHA-256
`1e75bb6ef4db64e47b391e53cbc5f8751c402509364ed9fc9b30266fbc922a1f`;
the report contains 889,339 bytes and has SHA-256
`a0c9710c3554aeb34b82cfbeb8c32e5ef6112833fb3cf28bfbd2e1d10e392119`.

The ZIP digest matches GitHub's advertised artifact digest, and its
sole member is byte-identical to the archived report. Independent
comparisons agree on all 18 verification-content fields, including
all 598 complete theorem records, four premise records, 167 input
hashes, nine dependency revisions, and the complete Lean inspection
output. Only `generated_at_utc` and `lake_build_output` differ.
At that checkpoint all 167 hashes matched its inspected files and the exact proof
tree `c1fc351aa09bac693b50db3d1f45d8f10efec08d`. All 30 frozen nondocument paths, including the
workflow, were checked against that proof tree. That accepted local report has
879,086 bytes, with the digest recorded above.
The [execution checkpoint](CHECKPOINT.md) records the exact proof,
run, job, artifact, timestamps, and complete 598-export scope. The
older evidence below retains its original scopes.

This historical Lemma 3.5 evidence does not cover the new 637-export Lemma 3.6 milestone.

### Earlier Lemma 3.4 verification

The preceding Lemma 3.4 milestone added 18 public theorem exports in
eight new modules, with 155 recorded input hashes including its
correspondence review. Strict targeted compilation and the root library
build passed under the pinned settings (3,166 build jobs).

**The full local aggregate verifier passed for all 571 theorem exports
and 128 Lean modules.** All 155 input hashes match the checked files.
All 553 preceding complete theorem records remain identical, including
their actual types, axiom lists, Lean source hashes, and scopes. All
18 new actual types and axiom lists match their prior inspections;
every new export uses exactly `Classical.choice`, `Quot.sound`, and
`propext`. The four registered literature premise records and nine
pinned dependency revisions are unchanged. All 28 frozen changed-file
hashes were preserved through verification, and the frozen manuscript
and PDF remain unchanged.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/169218f4b525d0433c2b53fdd49483f47623c1e8/certification/verification_report.json)
contains 833,730 bytes and has SHA-256
`e0bac7dc8881c3d8837d89fcf5a2b1a37056275256d0f6c8b20a749278e9a734`.
It records 14 Certified, zero Partial or Active, and 28 Pending numbered
results; all 33 auxiliary/supplementary groups remain Pending.

**The local and GitHub verifiers passed for the complete 571-export
scope.** [GitHub Actions run 43641041601, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43641041601)
succeeded at [proof commit 169218f](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/169218f4b525d0433c2b53fdd49483f47623c1e8),
with verification job `132588460975`. Its artifact `14131744612`
is preserved as the [original ZIP](certification/ci/run_43641041601_attempt_1.zip)
and [downloaded report](certification/ci/run_43641041601_attempt_1.json).
The ZIP contains 98,115 bytes and has SHA-256
`5544d79a2d678768bd00f19c8d55dd17b0dd60d7ec4010facee04f753fd1c2d2`;
the report contains 843,140 bytes and has SHA-256
`d6df7af8763ac77898b40940c71b3905c7371b8483f23138a74f53c6a087d0b6`.

The ZIP digest matches GitHub's advertised artifact digest, and its
sole member is byte-identical to the archived report. Independent
comparisons agree on all 18 verification-content fields, including
all 571 complete theorem records, four premise records, 155 input
hashes, nine dependency revisions, and the complete Lean inspection
output. Only `generated_at_utc` and `lake_build_output` differ.
All 155 hashes match the files inspected at that checkpoint and the
exact proof tree `008f5c69b8e7d04c4345eea285aa1e571b90cb23`. The local
report at that proof commit contains the exact 833,730 bytes with the
digest recorded above. The original artifact and report were preserved
in [evidence commit 77acba8](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/77acba81d1aa6024d8132500464fd66290b2665c),
whose tree is `3c3eca9779da8b87d9b3ab844e6c09eb41ae419b`.
The [execution checkpoint](CHECKPOINT.md) records the exact proof,
run, job, artifact, timestamps, and complete 571-export scope. This
evidence does not cover the new 598-export Lemma 3.5 milestone. The
older evidence below retains its original scopes.

### Earlier Lemma 3.3 verification

The preceding Lemma 3.3 milestone added 17 public theorem exports in
eight new modules, with 146 recorded input hashes including its
correspondence review.

**The full local aggregate verifier passed for all 553 theorem exports
and 120 Lean modules at that checkpoint.** All 146 input hashes match
the checked files.
All 536 preceding complete theorem records remain identical, including
their actual types, axiom lists, Lean source hashes, and scopes. All
17 new actual types and axiom lists match their prior inspections;
every new export uses exactly `Classical.choice`, `Quot.sound`, and
`propext`. The four registered literature premise records and nine
pinned dependency revisions are unchanged. All 29 frozen changed-file
hashes were preserved through verification, and the frozen manuscript
and PDF remain unchanged.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/b38301f89b01e424e5cf656da88ea3b56916423d/certification/verification_report.json)
contains 800,979 bytes and has SHA-256
`7760c9e3731c56567d2b0bd83eb2f5a5045acc3b5f93f78693d32084bd3e022d`.
It records 13 Certified, zero Partial or Active, and 29 Pending numbered
results; all 33 auxiliary/supplementary groups remain Pending.

**The local and GitHub verifiers passed for the complete 553-export
scope.** [GitHub Actions run 43637398379, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43637398379)
succeeded at [proof commit b38301f](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/b38301f89b01e424e5cf656da88ea3b56916423d),
with verification job `132577106792`. Its artifact `14130567360`
is preserved as the [original ZIP](certification/ci/run_43637398379_attempt_1.zip)
and [downloaded report](certification/ci/run_43637398379_attempt_1.json).
The ZIP contains 94,216 bytes and has SHA-256
`6f13223d4ddc910357e052aee24454d2bfe9ba9e7d96db23a60bda989a9933cf`;
the report contains 809,782 bytes and has SHA-256
`85aa7a67cc31680eca5197cfdb759e387076085cf69d54c9883b24dc097a33da`.

The ZIP digest matches GitHub's advertised artifact digest, and its
sole member is byte-identical to the archived report. Independent
comparisons agree on all 18 verification-content fields, including
all 553 complete theorem records, four premise records, 146 input
hashes, nine dependency revisions, and the complete Lean inspection
output. Only `generated_at_utc` and `lake_build_output` differ.
All 146 hashes match the files inspected at that checkpoint and the
exact proof tree `ebe28edb7e366b988bc88032f2525be7a507368c`. The local
report at that proof commit contains the exact 800,979 bytes with the
digest recorded above. The original artifact and report were preserved
in [evidence commit 642a0c8](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/642a0c8064bc3287be3660f132325adab4534624),
whose tree is `91ed8165569569a763e5e9fc364da5e4a17c8657`.
The [execution checkpoint](CHECKPOINT.md) records the exact proof,
run, job, artifact, timestamps, and complete 553-export scope. This
evidence does not cover the subsequent 571-export ramified milestone
or the preceding 598-export Lemma 3.5 milestone. The older evidence
below retains its original scopes.

The preceding Lemma 3.2 milestone added 54 public theorem exports in
16 new modules, with 137 recorded input hashes including its source
correspondence review.

**The full local and GitHub verifiers passed for the preceding 536-export
Gauss milestone.** All 112 modules were checked, and all 137 input
hashes match the files checked at that checkpoint.
All 54 new actual types and axiom lists match their prior inspections;
every new export uses exactly `Classical.choice`, `Quot.sound`, and
`propext`. All 482 preceding actual types, axiom lists, and Lean source
hashes remain unchanged. Of those records, 472 are identical in full;
the ten export scope descriptions for `PrimeQuadraticGauss.lean` only
replace the obsolete statement that full Lemma 3.2 remains Pending.
The four registered literature premise records and nine pinned
dependency revisions are unchanged. All 37
frozen changed-file hashes were preserved through verification, and
the frozen manuscript and PDF remain unchanged.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/2b3caedb1d46cafcfdc7e47d678bcfc654ef39d7/certification/verification_report.json)
contains 780,870 bytes and has SHA-256
`824069fc67d6f55812e9c9928c1461bb580564b92ee0f7e4cf1b252e59cd0699`.
It records 12 Certified, zero Partial or Active, and 30 Pending numbered
results; all 33 auxiliary/supplementary groups remain Pending.

[GitHub Actions run 43633148645, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43633148645)
succeeded at [proof commit 2b3caed](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/2b3caedb1d46cafcfdc7e47d678bcfc654ef39d7),
with verification job `132564011074`. Its artifact `14128654819` is
preserved as the [original ZIP](certification/ci/run_43633148645_attempt_1.zip)
and [downloaded report](certification/ci/run_43633148645_attempt_1.json).
The ZIP contains 91,228 bytes and has SHA-256
`0e46e53424a2264c3f0335a81bb9fbdff8bf25016342115213e5af3da6424d90`;
the report contains 788,811 bytes and has SHA-256
`403930110d44417d11827c61441cfb4a7e52e4f05f8f56432e0b993e35e9ce71`.

The ZIP digest matches GitHub's advertised artifact digest, and its
sole member is byte-identical to the archived report. All 18
verification-content fields exactly match the unchanged local report,
including all 536 complete theorem records, four premise records,
137 input hashes, nine dependency revisions, and the complete Lean
inspection output. Only `generated_at_utc` and `lake_build_output` differ.
All 137 hashes match the inspected files at that checkpoint and the
exact proof tree `dea151816197aafb69f94b3d9a7b885a24b63a5d`.
The report and original artifact were preserved in
[evidence commit cf3e902](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/cf3e90217e153d04ffd40a9636dceb29fc6fbc59).
The [execution checkpoint](CHECKPOINT.md) records the job, artifact,
timestamps, digests, and full 536-export scope. This evidence does not
cover the subsequent 553-export bound and 571-export ramified
milestones or the preceding 598-export Lemma 3.5 milestone. The older
evidence below retains its original scopes.

**The full local and GitHub verifiers passed for the preceding 482-export
CRT milestone.** All 96 modules passed the pinned strict checks, and all
120 recorded input hashes match the checked files. All 416 preceding
complete theorem records are identical, including their actual types,
axiom dependencies, source hashes, and scopes. The four registered
literature-input records and all nine pinned dependency revisions are
unchanged. All 66 new actual theorem types and axiom dependencies match
their prior inspections: 65 use `Classical.choice`, `Quot.sound`, and
`propext`; `residueLift_cast` uses only `Quot.sound` and `propext`.
No new export uses a literature premise. All 33 changed-file hashes
were preserved through the verification run, and the frozen manuscript
and PDF remain unchanged.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/0224dae194b48080f8af732dbf78580ffaab0c24/certification/verification_report.json)
contains 708,765 bytes and has SHA-256
`ec46cb57a7912faf2116faed95bc6021ed68a9ed78cfb28a05133c0df4515f0f`.
It records 11 Certified, zero Partial or Active, and 31 Pending numbered
results; all 33 auxiliary/supplementary groups remain Pending.

[GitHub Actions run 43626335642, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43626335642)
succeeded at [proof commit 0224dae](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/0224dae194b48080f8af732dbf78580ffaab0c24).
Its [downloaded report](certification/ci/run_43626335642_attempt_1.json)
and [original artifact ZIP](certification/ci/run_43626335642_attempt_1.zip)
are preserved. The ZIP digest matches GitHub's advertised digest, and
its sole report member is byte-identical to the archived JSON. All 18
verification-content fields exactly match the local report, including
all 482 complete theorem records, four premise records, 120 input hashes,
nine dependency revisions, and the complete Lean inspection output.
Only `generated_at_utc` and `lake_build_output` differ. All 120 hashes
also match the inspected files at that checkpoint and its exact proof
tree. The [execution checkpoint](CHECKPOINT.md) records the job,
artifact, digests, and full 482-export scope. This evidence does not
cover the new 536-export Gauss milestone. The older evidence below
retains its original scopes.

**The full local and GitHub verifiers passed for the preceding 416-export
pencil milestone.** All 84 modules
and 416 theorem exports passed the pinned strict checks, and all 107
recorded input hashes match the checked files. All 349 preceding full
theorem records, the four registered literature-input records, and all
nine pinned dependency revisions are unchanged. The actual types and
axiom dependencies of all 67 new exports match their prior inspections:
60 use only standard foundations, and seven additionally use the existing
Weil premise. The frozen manuscript and PDF remain unchanged.

The [local verification report at that proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/7da6aca687135b7c0f859873e69d5fe844b2cdac/certification/verification_report.json)
contains 620,000 bytes and has SHA-256
`d60c7a129061c59979ff52a1b79adca054ed97073fd0a527eb0a6d0663a1dca1`.
[GitHub Actions run 43618745198, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43618745198)
succeeded at [proof commit 7da6aca](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/7da6aca687135b7c0f859873e69d5fe844b2cdac).
Its [downloaded report](certification/ci/run_43618745198_attempt_1.json)
and [original artifact ZIP](certification/ci/run_43618745198_attempt_1.zip)
are preserved. The ZIP digest matches GitHub's advertised digest, and
its sole report member is byte-identical to the archived JSON. All 18
verification-content fields exactly matched that checkpoint's local report, including
all 416 theorem records, four premise records, 107 input hashes, nine
dependency revisions, and the complete Lean inspection output. Only the
run time and build log differed. All 107 hashes also matched the exact proof
tree and inspected files at that checkpoint. The [execution checkpoint](CHECKPOINT.md)
records the identifiers, digests, and complete 416-export scope. This
evidence does not cover the new CRT milestone. The older runs below
retain their original scopes.

**The full local and GitHub verifiers passed for the preceding diagonal
bad-prime milestone.**
All 71 modules and 349 theorem exports were checked under the pinned strict
settings. All 93 input hashes matched the files checked. The 325 previously
checked theorem records, including their actual types, axiom dependencies,
source hashes and scopes, are unchanged, as are the four registered
literature-input records and all nine pinned dependency revisions.
All 24 new exports use only `Classical.choice`, `Quot.sound`, and `propext`.
[GitHub Actions run 43614640507, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43614640507)
succeeded at [proof commit 09d7ea0](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6).
Its [downloaded report](certification/ci/run_43614640507_attempt_1.json)
and [original artifact ZIP](certification/ci/run_43614640507_attempt_1.zip)
are preserved. The artifact digest matches GitHub's advertised digest.
All 18 verification-content fields exactly match the local report,
including all 349 theorem records, four premise records, 93 input hashes,
nine dependency revisions, and the complete Lean inspection output.
Only the run time and build log differ. The [execution checkpoint](CHECKPOINT.md)
records the exact commit, run, artifact identifiers, digests, and scope.

**The full local and GitHub verifiers passed for the preceding polynomial Fourier checkpoint at
[proof commit 25dea29](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/25dea299d18e2a423404488ac1a923fded0cde7b):** all 66 modules and 325 theorem
exports were checked under the pinned strict settings. All 87 input hashes
matched the files checked at that proof commit, and all nine pinned dependency
revisions were unchanged. The 302 previously checked theorem types and axiom
dependencies and the four registered literature-input records were unchanged.
[GitHub Actions run 43611293071, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43611293071)
succeeded. Its [downloaded report](certification/ci/run_43611293071_attempt_1.json)
and [original artifact ZIP](certification/ci/run_43611293071_attempt_1.zip)
are preserved. All 325 theorem records, four premise records, 87 input
hashes, nine dependency revisions and the complete Lean inspection output
exactly matched that checkpoint's local report. Only the run time and build log differed.
The [execution checkpoint](CHECKPOINT.md) records the artifact identifiers,
digests and original 325-export scope. This evidence does not cover the new
diagonal-pencil milestone. The preserved runs below retain their stated preceding scopes.

**The full local and GitHub verifiers passed for the preceding exceptional-plane checkpoint at
[proof commit afdaf24](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/afdaf2497bcd76fdff8b658efef8e28f0388f5b7):** all 59 modules,
302 theorem exports, four exact registered literature premises and 80 input
hashes were checked under the pinned Lean settings. All 261 preceding
theorem types and axiom dependencies were unchanged at that checkpoint.
[GitHub Actions run 43608132418, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43608132418)
succeeded. Its [downloaded report](certification/ci/run_43608132418_attempt_1.json)
and [original artifact ZIP](certification/ci/run_43608132418_attempt_1.zip)
are preserved. All 80 input hashes, 302 theorem records, four literature-input
records and nine pinned dependency revisions exactly matched the local
verification. The [execution checkpoint](CHECKPOINT.md) records the artifact
identifiers, digests and complete scope.

**The full local and GitHub verifiers passed for the preceding bad-reduction,
height, and quadratic-trace checkpoint at
[proof commit cc87de7](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/cc87de7c88dc32339bb59636ac0127a19bbdde76):** all 50 modules,
261 proved exports, three registered literature premises, and 70 input
hashes were checked. Independent source reviews cover the exact Lang
interface, all of Lemma 4.1(i), and the complete Lemma 5.9.
[GitHub Actions run 43559876500, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43559876500)
succeeded. Its [downloaded report](certification/ci/run_43559876500_attempt_1.json)
and [original artifact ZIP](certification/ci/run_43559876500_attempt_1.zip)
are preserved. Artifact `14100255355` has ZIP SHA-256
`3ac9416897828dece4ccce6465aa58e0a2ceca5cdf29d4fe525277b4bbbf5ef5`.
All 70 hashes, 261 theorem records, three literature-input records, and pinned
dependency revisions matched that proof commit's local verification. This
preserved evidence records its original 261-export scope.

**The preceding Katz checkpoint passed locally and in [GitHub Actions](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43557804300)**
at [proof commit ef786b7](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/ef786b7f270a017dfce7ae702f1b720ff1084ef2): all 38 modules, 207 proved exports,
both exact literature premises, and 56 recorded input hashes were checked.
The [downloaded CI report](certification/ci/run_43557804300_attempt_1.json) and its
[original artifact ZIP](certification/ci/run_43557804300_attempt_1.zip) are preserved.
Their types, axiom dependencies, and input hashes matched the local verification
at that checkpoint.

**The preceding conic and plane-section checkpoint passed locally and in [GitHub Actions](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43553749446)**
at [proof commit 0fccf53](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/0fccf5379e067d349cb0f14b6dc226bc8096033b): all 31 modules, 162 proved exports,
the exact literature premise, and 47 recorded input hashes were checked.
The [downloaded CI report](certification/ci/run_43553749446_attempt_1.json) and its
[original artifact ZIP](certification/ci/run_43553749446_attempt_1.zip) are preserved.
Their types, axiom dependencies, and input hashes matched the local verification
at that checkpoint.

The preceding Weil and projective-line checkpoint passed locally and in
[GitHub Actions](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43551946447)
at [proof commit 450ff67](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/450ff678b56b0a32a76b848278b53ba697958939).
The downloaded CI report and original artifact are preserved in the repository.

- [Certification inventory, with links to checked exports](INVENTORY.md)
- [Dependency graphs and the proof structure](DEPENDENCIES.md)
- [Trusted literature inputs and excluded comparison claims](TRUSTED_INPUTS.md)
- [Live proof ledger](certification/status.json)
- [Actual Lean types and axiom dependencies](certification/verification_report.json)
- [Correspondence review for complete Lemma 3.8 and the corrected Euler product](certification/correspondence/local_density.md)
- [Correspondence review for complete Lemma 3.7 and dual-cone cancellation](certification/correspondence/cone_modulus_bound.md)
- [Correspondence review for complete Lemma 3.6 and its uniform modulus bound](certification/correspondence/generic_modulus_bound.md)
- [Correspondence review for both clauses of Lemma 3.5 and the actual global complete sums](certification/correspondence/good_global_complete_sum.md)
- [Correspondence review for complete Lemma 3.4 and the actual ramified complete sum](certification/correspondence/ramified_complete_sum.md)
- [Correspondence review for complete Lemma 3.3 and the uniform complete-sum bound](certification/correspondence/bad_prime_bound.md)
- [Correspondence review for complete Lemma 3.2 and the actual prime-power Gauss sums](certification/correspondence/prime_power_gauss.md)
- [Correspondence review for complete Lemma 3.1 and the literal complete sums](certification/correspondence/complete_sum_crt.md)
- [Correspondence review for complete Lemma 4.6 and the diagonal pencil](certification/correspondence/diagonal_pencil.md)
- [Correspondence review for complete Lemma 4.5 and the exact diagonal modulus](certification/correspondence/diagonal_bad_primes.md)
- [Correspondence review for complete Lemma 4.4 and the Fourier ray identity](certification/correspondence/fourier_rays.md)
- [Correspondence review for the quadratic trace](certification/correspondence/quadratic_trace.md)
- [Correspondence review for the Weil input](certification/correspondence/weil_input.md)
- [Correspondence review for the projective-line bound](certification/correspondence/projective_weil.md)
- [Correspondence review for the uniform conic parametrization](certification/correspondence/conic_parametrization.md)
- [Correspondence review for the plane-section bound](certification/correspondence/plane_section.md)
- [Source review for the composite Katz/Fulton interface](certification/correspondence/katz_input.md)
- [Correspondence review for the quadric Katz bound](certification/correspondence/katz_quadric.md)
- [Source review for the generic resultant input](certification/correspondence/elimination_input.md)
- [Correspondence review for bad-prime finiteness and height](certification/correspondence/bad_reduction.md)
- [Source review for the composite Bertini and projective-Jacobian input](certification/correspondence/bertini_input.md)
- [Latest execution checkpoint](CHECKPOINT.md)

![Principal proof dependencies](docs/dependency_overview.png)

[Full dependency graph (PNG)](docs/dependency_graph.png) ·
[Overview (PNG)](docs/dependency_overview.png) ·
[Full graph as a zoomable PDF](docs/dependency_graph.pdf)

## Certification scope

Cited literature inputs used in the proofs are trusted. We formalize their
precise interfaces, verify their hypotheses, and prove the manuscript's
deductions. The disputed estimates that this paper corrects are recorded as
comparison targets, not assumptions.

A numbered result is certified only after every clause has a kernel-checked
proof and its formal statement and dependencies have been matched to the
frozen source. Counts refer to numbered results, not supporting declarations.
Supplementary mathematical claims and a final whole-paper correspondence review
are tracked separately.

Four external Lean premises are registered. The first is the simple-root
univariate Weil estimate from [K, equation (1.2)]. The second is the general
surface spectral interface in [Trusted/Katz.lean](QuaternaryQuadraticForms/Trusted/Katz.lean).
That interface is explicitly composite: Katz's concentration, purity, and
trace formula are combined with the general hypersurface geometry,
adjunction, and degree formulas documented from Fulton and the standard
Jacobian interpretation. It is registered against both `EXT.KATZ` and
`EXT.HYPERSURFACE_CHERN`. Its conclusion supplies spectral data and an
unevaluated general Chern coefficient for arbitrary hypersurface degree.

The [source review](certification/correspondence/katz_input.md) records this
boundary. The repository does not formalize schemes, Chern classes, or
étale cohomology. It does prove the actual quadric's geometric hypotheses,
the coefficient `2n²−4n+4`, and the triangle-inequality deduction. The
projective-line and plane-section estimates use the separate Weil input.
The geometric and arithmetic deductions are internal proofs.

The third premise is Lang's general homogeneous resultant system in
[Trusted/Elimination.lean](QuaternaryQuadraticForms/Trusted/Elimination.lean),
registered as `EXT.LANG_ELIMINATION`. Its integer resultant polynomials
are chosen before the coefficient field and generic coefficient assignment.
The [source review](certification/correspondence/elimination_input.md)
matches this interface to Lang, *Algebra*, IX.4.1, p. 402, with the
algebraic-closure convention following IX.3.1. Substitution of polynomial
parameters, the actual gradient equations, the common nonzero integer,
bad-prime finiteness, and the uniform coefficient-height bound are all
proved internally.

The fourth premise is the general homogeneous tangent-space interface in
[Trusted/Bertini.lean](QuaternaryQuadraticForms/Trusted/Bertini.lean),
registered against both `EXT.HARTSHORNE_BERTINI` and
`EXT.PROJECTIVE_JACOBIAN`. It combines Hartshorne II.8.18, pp. 179–180,
with the general projective Jacobian criterion, dimension and component
facts, and the tangent-space interpretation documented in the
[source review](certification/correspondence/bertini_input.md). For `c`
homogeneous equations of positive assigned degrees in `N` coordinates,
with `c + 2 ≤ N` and full Jacobian rank over an algebraically closed field,
it supplies a hyperplane whose functional is nonzero on a common tangent
vector at every intersection point. The formalization proves
the resulting rank increase, the specialization to `F,G`, the second
elimination system, descent to the prime field, the uniform degree bound,
and the construction of `D_p` internally. The premise asserts no resultant,
bad-prime modulus, exceptional polynomial, or character-sum estimate.

## The projective-line estimate

For a nonzero homogeneous binary form of degree `n ≥ 2` with `n` distinct
projective zeros over the algebraic closure, a nonprincipal character `ψ`
satisfying `ψ ^ n = 1` gives

$$\left|\sum_{P\in\mathbf P^1(\mathbf F_p)}\psi(g(P))\right|
\le (n-1)\sqrt p+1.$$

The proof constructs the actual projective charts `(z:1)` and `(1:0)` and
uses the literal polynomial `g(X,1)`. Counting the geometric zeros proves
that its degree is `n` or `n−1`, and that all its roots are distinct. This
supplies every hypothesis of the registered Weil input. The point at infinity
has a character value of norm at most one.

| Module | Checked contribution |
|---|---|
| [ProjectiveLine](QuaternaryQuadraticForms/ProjectiveLine.lean) | Actual projective charts, the sum decomposition, and the corresponding zero-set equivalence |
| [BinaryForms](QuaternaryQuadraticForms/BinaryForms.lean) | Literal substitution, coefficient extension, homogenization recovery, and degree calculation |
| [GeometricRoots](QuaternaryQuadraticForms/GeometricRoots.lean) | Root-count bounds and equivalence with separability over the algebraic closure |
| [BinaryFormRoots](QuaternaryQuadraticForms/BinaryFormRoots.lean) | Derivation of the positive affine degree and simple-root condition from the projective geometric roots |
| [WeilBound](QuaternaryQuadraticForms/WeilBound.lean) | Lemma 2.5 as an exact application of the separately [registered literature premise](QuaternaryQuadraticForms/Trusted/Weil.lean) |
| [ProjectiveWeil](QuaternaryQuadraticForms/ProjectiveWeil.lean) | Complete Corollary 2.6 under the literal manuscript hypotheses |

## The conic and plane-section estimates

For a good prime `p ∤ 2 |det A|` and `F*(u) ≠ 0`, Lemma 4.2 constructs a
single tuple `μ` of binary quadratic polynomials over `ZMod p`. For every field
extension `k`, the same polynomials, with their coefficients mapped to `k`, give
a bijection from `P¹(k)` onto the projective points satisfying
`F(x) = u · x = 0`. The two vectors of formal partial derivatives of `μ` are
linearly independent at every nonzero parameter vector, including over the
algebraic closure.

The construction proves the existence of an isotropic vector and a basis in
which the restricted form is `y₀ y₁ + a y₂²`, with `a ≠ 0`. In that basis the
parametrization is `(-a s², t², st)`. Its embedding into four coordinates,
polynomial identities, and compatibility with every field extension are
proved. The projective equivalence is tied to the evaluation of these actual
coordinate polynomials on every representative.

For Lemma 4.3, the hypothesis is the literal rank-three condition on
`(∇F(x), ∇G(x), u)` at every nonzero geometric common zero. The formal chain
rule and the independent derivative vectors show that `G ∘ μ` cannot have a
singular projective zero. The degree-`2n` binary form therefore has exactly
`2n` distinct geometric projective zeros. This argument uses Euler's identity
without dividing by the degree, so it also covers characteristics dividing
`n` or `2n`.

Transporting the actual section trace along the constructed bijection and
applying Corollary 2.6 gives

$$\left|\sum_{\substack{P\in\mathcal Q(\mathbf F_p)\\u\cdot P=0}}
\psi(G(P))\right|\le (2n-1)\sqrt p+1.$$

Representative independence is proved from homogeneity and `ψ ^ n = 1`.
The final theorem starts from the manuscript's integral symmetric matrix,
good-prime condition, and geometric transversality hypothesis; it constructs
the required parametrizations inside the proof.

| Module | Checked contribution |
|---|---|
| [QuadraticPlane](QuaternaryQuadraticForms/QuadraticPlane.lean), [ConicNormalForm](QuaternaryQuadraticForms/ConicNormalForm.lean) | Nondegeneracy and isotropy of the plane restriction, and the ternary hyperbolic basis |
| [ConicCharts](QuaternaryQuadraticForms/ConicCharts.lean), [ConicPolynomials](QuaternaryQuadraticForms/ConicPolynomials.lean) | Actual projective bijection for the canonical conic, homogeneous coordinates, and formal derivatives |
| [ScalarExtension](QuaternaryQuadraticForms/ScalarExtension.lean), [GoodPrime](QuaternaryQuadraticForms/GoodPrime.lean) | Extension of the fixed coordinates to every field, and reduction under the exact good-prime condition |
| [PlaneConic](QuaternaryQuadraticForms/PlaneConic.lean), [EmbeddedConic](QuaternaryQuadraticForms/EmbeddedConic.lean) | The literal projective plane section, its polynomial parametrization, and the defining polynomial identities |
| [ConicParametrization](QuaternaryQuadraticForms/ConicParametrization.lean) | Complete Lemma 4.2, including one tuple valid over every extension field |
| [PolynomialChainRule](QuaternaryQuadraticForms/PolynomialChainRule.lean), [TransversePullback](QuaternaryQuadraticForms/TransversePullback.lean), [TransversalityRank](QuaternaryQuadraticForms/TransversalityRank.lean) | Formal differentiation of the pullback and conversion of the literal rank-three hypothesis to the tangent-space contradiction |
| [BinaryNonsingular](QuaternaryQuadraticForms/BinaryNonsingular.lean) | Distinct geometric projective zeros, including infinity, with no characteristic-degree restriction |
| [PlaneSectionBound](QuaternaryQuadraticForms/PlaneSectionBound.lean), [PlaneSectionTheorem](QuaternaryQuadraticForms/PlaneSectionTheorem.lean) | Transport of the literal character sum and complete Lemma 4.3 under the manuscript hypotheses |

## The quadric Katz estimate

Lemma 2.7 is proved for the actual projective trace:

$$\left|\sum_{P\in\mathcal Q(\mathbf F_p)}\psi(G(P))\right|
\le (2n^2-4n+4)p.$$

The final theorem starts with the integral symmetric matrix, the condition
`p ∤ 2 |det A|`, the homogeneous form `G` of degree `n ≥ 2`, and the actual
rank-two gradient condition over the algebraic closure. The character is
nonprincipal and satisfies `ψ ^ n = 1`. There is no assumption that the
characteristic be prime to `n`.

The formal gradient is proved to be `2 A x`, which gives geometric
smoothness from nonsingularity of the reduced matrix. Geometric
irreducibility is also proved: a factorization of the quadratic polynomial
into affine-linear factors would force its gradient image into the span of
two fixed vectors, contradicting nonsingularity in four dimensions. The
transverse polynomial is proved nonzero using an actual nonzero quadric
point and the rank-two condition.

The general source input then supplies complex numbers of norm `p` whose
sum is the actual projective trace. Its dimension is the unevaluated Chern
coefficient. Integer polynomial arithmetic proves

$$2[T^2]\big((1+2T+2T^2)(1-nT+n^2T^2)\big)=2n^2-4n+4,$$

and the finite-sum triangle inequality gives the bound. The identification
of the general hypersurface sum with the matrix-quadric trace is proved
explicitly. These quadric deductions are not part of the trusted premise.

| Module | Contribution |
|---|---|
| [QuadricSmooth](QuaternaryQuadraticForms/QuadricSmooth.lean) | Actual formal gradient, exact degree, and smoothness and irreducibility over every extension field |
| [ProjectiveSurfaceTrace](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean) | Actual projective hypersurface points and sum, identification with the quadric trace, and nonvanishing of the transverse polynomial |
| [SurfaceChern](QuaternaryQuadraticForms/SurfaceChern.lean) | General coefficient algebra, the exact quadric coefficient, and the finite complex-sum norm bound |
| [Trusted/Katz](QuaternaryQuadraticForms/Trusted/Katz.lean) | The separately registered composite literature interface for general hypersurfaces |
| [KatzBound](QuaternaryQuadraticForms/KatzBound.lean) | Complete Lemma 2.7 from the manuscript's literal hypotheses |
| [GoodReduction](QuaternaryQuadraticForms/GoodReduction.lean) | The exact bad-prime set and `N_G`, its prime-divisor characterization, and arithmetic finiteness from a nonzero elimination witness |
| [QuadraticTraceBound](QuaternaryQuadraticForms/QuadraticTraceBound.lean) | The bound `4p` and its combination with integrality and divisibility under good reduction; the final source theorem is assembled in `QuadraticTraceTheorem.lean` |

## Checked finite-field branch

The formalization uses four-coordinate vectors over `ZMod p`, the quadratic
form `xᵀ A x`, actual homogeneous multivariate polynomials, multiplicative
characters extended by zero, and the standard complex additive character.
Projective points are mathlib's quotient by nonzero scalar multiplication.
The quadric, hyperplane condition, and weight are proved independent of the
chosen representative.

| Module | Checked contribution |
|---|---|
| [PolynomialWeights](QuaternaryQuadraticForms/PolynomialWeights.lean) | Polynomial scaling, reduction of integral coefficients, and all three weight properties in (3.1) |
| [FiniteCharacters](QuaternaryQuadraticForms/FiniteCharacters.lean) | The additive-character sum over nonzero scalars: `p − 1` at zero and `−1` otherwise |
| [ProjectiveRays](QuaternaryQuadraticForms/ProjectiveRays.lean) | A proved parametrization of nonzero vectors by projective points and field units, and the resulting sum decomposition |
| [RayAlgebra](QuaternaryQuadraticForms/RayAlgebra.lean) | Finite algebra combining the ray contributions |
| [FourierRays](QuaternaryQuadraticForms/FourierRays.lean) | The literal identity (4.5), its zero-frequency case, and specialization to integral input data |
| [MatrixPolynomial](QuaternaryQuadraticForms/MatrixPolynomial.lean) | A homogeneous polynomial representing `xᵀ A x`, with its degree bound proved |
| [QuadraticCharacter](QuaternaryQuadraticForms/QuadraticCharacter.lean) | Identification of the integer quadratic character, its complex cast, and the Legendre symbol |
| [AffineDivisibility](QuaternaryQuadraticForms/AffineDivisibility.lean) | Divisibility of the integer affine character sum, using polynomial-sum vanishing over the prime field |
| [QuadraticTrace](QuaternaryQuadraticForms/QuadraticTrace.lean) | Integrality and divisibility of the actual projective trace, including integral input coefficients |

Writing `a` for the projective trace and `a_u` for the hyperplane-section trace,
the checked identity is

$$C_p(u)=p a_u-a,$$

including `a_0 = a`, hence $C_p(0)=(p-1)a$. Reduction of an integral frequency
is proved to be zero exactly when `p` divides each coordinate.

These identities require only positive degree and `ψ ^ n = 1`; nonsingularity,
smoothness, and nonprincipality are unnecessary for this part of the proof.
The manuscript's hypotheses therefore specialize the checked results.

## Local densities and the corrected Euler product

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

## Cancellation of the modulus sum on the dual cone

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

## The absolute modulus estimate away from the dual cone

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

## The global complete-sum identities

[GoodGlobalTheorem.lean](QuaternaryQuadraticForms/GoodGlobalTheorem.lean)
proves `source_good_global_complete_sum`, containing both clauses of
Lemma 3.5. For squarefree $q\ge1$, $(q,N)=1$, $c\ge1$, and the
literal factors $q_1=\gcd(q,c)$, $q_2=q/q_1$, the good-modulus clause is

$$\mathcal S_{q,c}(u)
=C_{q_2}(u)\,q_1c^2\chi(q_1c)\,
\xi_{q_1}(\operatorname{adj}(A)u)\,
R_{q_1c}(F^*(u)),\qquad(c,N_F)=1.$$

On the dual cone the complete second clause is

$$\mathcal S_{q,c}(u)
=C_{q_2}(u)\,q_1^2\chi(q_1)\,
\xi_{q_1}(\operatorname{adj}(A)u)\,S_c(u),
\qquad F^*(u)=0,\quad c\ge1.$$

The second identity includes every bad-prime factor of `c` and every
zero value of the sums. Both statements concern the existing
`mixedCompleteSum`, `constrainedFourierSum`, and `unweightedCompleteSum`.
The adjugate and dual value are the actual integer matrix expressions.
The right-hand weight is `sourceCompositeWeight`, the literal product
of the original supplied functions at the prime divisors of `q₁`.
Its equality with the extended-family representation inside the sums
is proved.

`GlobalQuadraticCharacter.lean` uses the actual Jacobi symbol
`globalQuadraticChar α n = (jacobiSym α n : ℂ)` as an intermediate
coefficient. It proves multiplicativity and the exact prime-power
Legendre values. Prime induction then proves agreement, at every
positive modulus coprime to `2 |α|`, with an actual supplied
`DirichletCharacter ℂ M` having the source's stated good-prime values.
The source endpoints use that original `χ`; agreement at composite
moduli is a conclusion of the proof. These identities do not require
primitivity, a particular conductor, or nonsquareness of `α`.

The Ramanujan factors are the actual unit sums. Their multiplicativity
is proved by the scaled unit CRT bijection and the standard additive
character; their value at zero is the unit count $\varphi(n)$.
For `d ∣ c`, the proved arithmetic identity
$\varphi(dc)=d\varphi(c)$ supplies the extra factor on the dual cone.
All modulus-one conventions are included.

For squarefree `q ∣ c`, induction over prime powers and coprime
products proves the shared-support formula. A squarefree divisor of
$p^k$ is proved to be `1` or `p`, so the actual formulas of Lemmas
3.2 and 3.4 apply. In a coprime split `c = mn`, the factors are the
actual `gcd(q,m)` and `gcd(q,n)`. Their product, squarefreeness,
divisibility, and full CRT-block coprimality are proved. The general
case then separates $C_{q_2}(u)$ by the actual CRT theorem, using the
proved coprimality of `q₂` and `q₁ c`.

For an arbitrary modulus on the dual cone, the proof constructs
$c=bg$, with coprime positive factors, every prime of `b` dividing
`N_F`, and `(g,N_F)=1`. The source radical condition and `(q,N)=1`
prove `(q,N_F)=1`, hence `(q,b)=1` and `gcd(q,c)=gcd(q,g)`. The two
actual CRT identities retain the same factor:

$$\mathcal S_{q,c}(u)=S_b(u)\mathcal S_{q,g}(u),\qquad
S_c(u)=S_b(u)S_g(u).$$

Multiplying the good-part cone identity by $S_b(u)$ proves the result,
including when that factor vanishes. No character sum is cancelled.

The source theorem assumes symmetry, integer nonsingularity, the
literal radical divisibility, the supplied character's good-prime
values, and scalar invariance of the supplied prime functions. It
needs neither their norm bound nor their value at zero, and imposes
no exceptional frequency-stratum hypothesis. The separate source
condition `N ≥ 1` is unused here; it is not inferred from `(q,N)=1`,
which also permits `q=1, N=0`.

| Modules | Checked contribution |
|---|---|
| [GlobalQuadraticCharacter](QuaternaryQuadraticForms/GlobalQuadraticCharacter.lean) | Actual Jacobi coefficients and proved agreement with the source Dirichlet character |
| [RamanujanMultiplicativity](QuaternaryQuadraticForms/RamanujanMultiplicativity.lean) | Actual unit CRT, zero frequency, and the shared-factor totient identity |
| [SquarefreeGcdFactors](QuaternaryQuadraticForms/SquarefreeGcdFactors.lean), [ModulusPrimeSplit](QuaternaryQuadraticForms/ModulusPrimeSplit.lean) | The literal gcd/quotient factors and constructed bad/good modulus split |
| [GoodUnweightedCompleteSum](QuaternaryQuadraticForms/GoodUnweightedCompleteSum.lean), [SharedSupportCompleteSum](QuaternaryQuadraticForms/SharedSupportCompleteSum.lean) | Prime-power and CRT assembly for actual good-modulus sums |
| [GoodGlobalCompleteSum](QuaternaryQuadraticForms/GoodGlobalCompleteSum.lean), [ConeCompleteSum](QuaternaryQuadraticForms/ConeCompleteSum.lean) | Both identities, with the cone clause at every positive modulus |
| [SourceCompositeWeights](QuaternaryQuadraticForms/SourceCompositeWeights.lean), [SourceGoodModulus](QuaternaryQuadraticForms/SourceGoodModulus.lean), [GoodGlobalTheorem](QuaternaryQuadraticForms/GoodGlobalTheorem.lean) | Original supplied weights, the source radical deduction, and the bundled source theorem |

The [source correspondence review](certification/correspondence/good_global_complete_sum.md)
checks both clauses, the source character agreement, and the complete
bad-prime extension. No literature premise is used.

## The ramified complete-sum identity

[RamifiedCompleteSum.lean](QuaternaryQuadraticForms/RamifiedCompleteSum.lean)
proves both `ramified_complete_sum` at the literal good-prime modulus
and `source_ramified_complete_sum` under the source's condition
$p\nmid N$. For every $k\ge1$ and $u\in\mathbb Z^4$,

$$\mathcal S_{p,p^k}(u)
=\chi(p)^{k+1}p^{2k+1}\,
\xi_p(\operatorname{adj}(A)u)\,
R_{p^{k+1}}(F^*(u)).$$

All objects are the existing literal definitions: the mixed complete
sum, the Legendre symbol of the integer determinant, the actual
adjugate vector and dual value, and the unit-defined Ramanujan sum.
The source wrapper accepts weights supplied only at primes outside
`N` and returns the original supplied function on its right-hand side.
The hypotheses `A.det ≠ 0`, `rad(N_F) ∣ N`, and `p ∤ N` prove
`p ∤ N_F`, where `N_F = 2 |det A|`. Nonsingularity is needed in this
radical deduction because the existing radical at zero is an empty
product. The separate source assumption `N ≥ 1` follows already from
`p ∤ N` for the selected prime.

The new actual sum is

$$\mathcal U_j(u)=\sum_{a\bmod p^j}^{*}\sum_{x\bmod p^j}
\xi_p(x)e_{p^j}(aF(x)+u\cdot x),\qquad j\ge2.$$

`weightedIntegralGaussSum` defines each inner sum using canonical
integer representatives; `primeWeightedCompleteSum` sums these inner
sums over actual residue units. Splitting $x=y+p^{j-1}z$ preserves
the weight modulo `p`, and the exact quadratic phase leaves the
linear term $(2aAy+u)\cdot z$. Four-coordinate orthogonality selects
precisely $2aAy+u=0\pmod p$. Multiplying by the adjugate gives

$$\operatorname{adj}(A)u=-(2a\det A)y\pmod p.$$

The scalar is nonzero at the good prime. The supplied nonzero-scalar
invariance therefore extracts exactly $\xi_p(\operatorname{adj}(A)u)$,
also when the frequency is zero. The already proved Lemma 3.2 then
evaluates the remaining actual complete sum:

$$\mathcal U_j(u)=\chi(p)^j p^{2j}\,
\xi_p(\operatorname{adj}(A)u)R_{p^j}(F^*(u)).$$

The actual unit bijection $(a,t)\mapsto a+c t$ modulo $pc$, valid
when $p\mid c$, preserves canonical integer values. Orthogonality
in `t` contributes `p` exactly when $p\mid F(x)$, which is the
existing cone condition in the mixed sum. Consequently,

$$\mathcal U_{k+1}(u)=p\mathcal S_{p,p^k}(u).$$

The final theorem cancels this nonzero scalar `p` and combines the
powers to obtain `2k+1`. No character sum or Ramanujan value is
cancelled. The proof covers every frequency, including $p\mid u$
and $p\mid F^*(u)$. It needs only scalar invariance of the weight;
its value at zero and norm bound, the Section 3 exceptional frequency
strata, and nonsquareness of the determinant are unnecessary here.

| Modules | Checked contribution |
|---|---|
| [WeightedGaussSums](QuaternaryQuadraticForms/WeightedGaussSums.lean) | Literal weighted inner and unit sums, with exact weight-one bridges |
| [WeightedGaussStationaryPhase](QuaternaryQuadraticForms/WeightedGaussStationaryPhase.lean) | Actual residue digits, unchanged weight, and the stationary-gradient indicator |
| [WeightedGaussExtraction](QuaternaryQuadraticForms/WeightedGaussExtraction.lean) | Adjugate multiplication and extraction by nonzero-scalar invariance |
| [WeightedCompleteSum](QuaternaryQuadraticForms/WeightedCompleteSum.lean) | Exact evaluation of the actual weighted complete sum at every exponent at least two |
| [PrimePowerUnitDigits](QuaternaryQuadraticForms/PrimePowerUnitDigits.lean), [RamifiedUnitLift](QuaternaryQuadraticForms/RamifiedUnitLift.lean) | The actual unit digit bijection and the exact factor `p` selecting the cone |
| [SourceGoodPrime](QuaternaryQuadraticForms/SourceGoodPrime.lean), [RamifiedCompleteSum](QuaternaryQuadraticForms/RamifiedCompleteSum.lean) | The source radical deduction and the complete Lemma 3.4 formula |

The [source correspondence review](certification/correspondence/ramified_complete_sum.md)
checks the exact objects, exponents, unit parametrization, and source
hypotheses. No literature premise is used.

## The uniform complete-sum bound

[BadPrimeBound.lean](QuaternaryQuadraticForms/BadPrimeBound.lean) proves
`bad_prime_bound`, the full statement of Lemma 3.3:

$$|S_c(u)|\le4\sqrt{|\det A|}\,c^3\qquad(c\ge1,\ u\in\mathbb Z^4).$$

Here `S_c` is the existing `unweightedCompleteSum`, with its actual
unit parameter and four residue coordinates. The final theorem assumes
`A.transpose = A` and `A.det ≠ 0` over the integers. Positive moduli
are represented by `c : ℕ` with `[NeZero c]`. The theorem includes
modulus one, arbitrary composite moduli, and every frequency. It needs
neither a good-prime condition nor nonsquareness of the determinant.

For each actual unit parameter $a$, put
$V_c(a,u)=\sum_{x\bmod c}e_c(aF(x)+u\cdot x)$ and let
$K_c(2A)=\{z\bmod c:2Az=0\}$. The checked translation identity is

$$V_c(a,u)\overline{V_c(a,u)}
=c^4\sum_{z\in K_c(2A)}e_c(aF(z)+u\cdot z).$$

It follows by reindexing the actual pair of vectors as $x,x+z$,
expanding the symmetric quadratic form, and applying the standard
character's orthogonality at the composite modulus. Invertibility of
$a$ removes that scalar from the kernel condition. The triangle
inequality then gives $|V_c(a,u)|^2\le c^4|K_c(2A)|$.

The kernel estimate uses a determinant/index form of the manuscript's
Smith normal-form argument. For a nonsingular integer `4 × 4` matrix `B`,
mathlib's proved determinant-index theorem identifies the index of
$B\mathbb Z^4$ in $\mathbb Z^4$ with $|\det B|$. Coordinate reduction
is surjective and takes this actual range onto the range of `B`
modulo `c`, whose index therefore divides the integer index. For the
finite residue endomorphism, the range index is precisely the kernel
cardinality. Consequently,

$$|K_c(B)|\mid |\det B|,\qquad |K_c(B)|\le|\det B|.$$

Applying this to `B = 2 • A`, with the exact identity
$\det(2A)=16\det A$, yields
$|V_c(a,u)|^2\le16|\det A|c^4$. Nonnegative square roots give the
factor $4\sqrt{|\det A|}c^2$. Finally, the actual unit group has at
most `c` elements, so summing its inner bounds proves the source
estimate.

| Modules | Checked contribution |
|---|---|
| [GaussNorm](QuaternaryQuadraticForms/GaussNorm.lean) | Composite-modulus orthogonality, the exact kernel phase, and the squared-norm inequality |
| [MatrixResidueKernel](QuaternaryQuadraticForms/MatrixResidueKernel.lean), [IntegerMatrixKernelBound](QuaternaryQuadraticForms/IntegerMatrixKernelBound.lean) | The actual residue kernel and its determinant bound through range-index divisibility |
| [DoubledMatrixKernel](QuaternaryQuadraticForms/DoubledMatrixKernel.lean) | Identification of the selected kernel with the reduction of the doubled integer matrix |
| [GaussBoundConstants](QuaternaryQuadraticForms/GaussBoundConstants.lean) | The factor sixteen in the determinant, the factor four after square roots, and the actual unit-count bound |
| [BadPrimeGaussBound](QuaternaryQuadraticForms/BadPrimeGaussBound.lean) | The full inner Gauss bound for integral matrices and every modulus |
| [CompleteSumNorm](QuaternaryQuadraticForms/CompleteSumNorm.lean), [BadPrimeBound](QuaternaryQuadraticForms/BadPrimeBound.lean) | Summation over actual units and the final literal complete-sum estimate |

The [source correspondence review](certification/correspondence/bad_prime_bound.md)
checks the kernel argument, exact constants, and every source quantifier.
The determinant/index theorem is proved in the pinned mathlib using
Smith normal form. No literature premise or assumed inner bound remains
in the final theorem.

## Complete prime-power Gauss evaluation

The single theorem
[prime_power_gauss](QuaternaryQuadraticForms/PrimePowerGaussTheorem.lean)
contains every clause of Lemma 3.2. Let `A` be the source's symmetric
integral matrix, write $\alpha=\det A$ and
$F^*(u)=u^{\mathsf T}\operatorname{adj}(A)u$, and let
$\chi(p)=(\alpha/p)$ be the actual Legendre symbol. Under the literal
condition $p\nmid N_F=2|\alpha|$, for every $k\ge1$ and integral
frequency $u$, it proves

$$\sum_{x\bmod p^k}e_{p^k}(aF(x)+u\cdot x)
=\chi(p)^k p^{2k}
 e_{p^k}\!\left(-\overline{4a\alpha}\,F^*(u)\right)
\qquad(p\nmid a),$$

$$S_{p^k}(u)=\chi(p)^k p^{2k}R_{p^k}(F^*(u)),$$

$$\#\mathcal Q(\mathbb F_p)=p^2+(1+\chi(p))p+1.$$

The Gauss sum is the literal sum over `(ZMod (p^k))⁴` with the standard
positive additive character. The integer coefficient, matrix, and
frequency reductions agree with the source's representative sum.
`S_{p^k}` is the existing unweighted complete sum, `R_{p^k}` is the
actual sum over residue units, and the point count concerns the
existing projective quadric.

| Modules | Checked contribution |
|---|---|
| [GeneralPrimeGauss](QuaternaryQuadraticForms/GeneralPrimeGauss.lean) | The prime base case for every nonsingular symmetric matrix, via an actual orthogonal basis and the determinant-square identity |
| [PrimePowerResidues](QuaternaryQuadraticForms/PrimePowerResidues.lean), [PrimePowerGaussRecurrence](QuaternaryQuadraticForms/PrimePowerGaussRecurrence.lean) | Actual residue-digit bijections and additive orthogonality proving the two-step recurrence |
| [MatrixSquareCompletion](QuaternaryQuadraticForms/MatrixSquareCompletion.lean), [IntegralGaussShift](QuaternaryQuadraticForms/IntegralGaussShift.lean) | Square completion with the actual adjugate and the exact modular inverse in the source phase |
| [PrimePowerGauss](QuaternaryQuadraticForms/PrimePowerGauss.lean) | The closed pure and shifted formulas and the pure value for every actual residue unit |
| [RamanujanSums](QuaternaryQuadraticForms/RamanujanSums.lean), [UnramifiedCompleteSum](QuaternaryQuadraticForms/UnramifiedCompleteSum.lean) | The reciprocal unit permutation and the exact formula for the existing `S_{p^k}` |
| [QuadricCounting](QuaternaryQuadraticForms/QuadricCounting.lean), [QuadricPointCount](QuaternaryQuadraticForms/QuadricPointCount.lean) | Additive orthogonality, the affine zero count, and the cardinality of the actual projective quadric |

For the prime base case, the constructed change of basis `P` gives
$P^{\mathsf T}AP=\operatorname{diag}(d_i)$ and
$\prod_i d_i=(\det P)^2\det A$, with every $d_i$ and $\det P$ nonzero.
The quadratic character removes that square, and the previously checked
scalar Gauss identities give $V_1(a)=\chi(p)p^2$. No diagonalization
hypothesis remains in the endpoint.

The digit decomposition proves $V_{k+2}(a)=p^4V_k(a)$ for every
$k\ge0$, including the actual modulus-one value $V_0(a)=1$.
Together with the prime base case this gives
$V_k(a)=\chi(p)^k p^{2k}$. The source good-prime condition supplies
the units needed for square completion. The pure and shifted integral
formulas extend to $k=0$; the canonical unit lift and the final
Ramanujan theorem use the source range $k\ge1$.

The map $a\mapsto-\overline{4a\alpha}$ is proved to permute the actual
units, so summing the shifted formula gives the Ramanujan identity.
For the last clause, the zero scalar is retained in additive
orthogonality, giving the affine count
$p^3+\chi(p)(p^2-p)$. Removing the actual origin and using the proved
partition into projective rays gives the displayed projective count.
The complete [source correspondence review](certification/correspondence/prime_power_gauss.md)
checks all three clauses and their arithmetic hypotheses. No new
literature premise is used.

## Complete CRT factorization of the local sums

Lemma 3.1 concerns the source's generic local functions `ξ_p`, with
invariance under nonzero scalar multiplication. The actual composite
weight is

$$\xi_q(x)=\prod_{p\mid q}\xi_p(x\bmod p),\qquad \xi_1(x)=1.$$

`CompleteSums.lean` defines the literal sums on their residue classes:

$$C_q(u)=\sum_{\substack{x\bmod q\\q\mid F(x)}}
\xi_q(x)e_q(u\cdot x),\qquad
S_c(u)=\sum_{a\bmod c}^{*}\sum_{x\bmod c}e_c(aF(x)+u\cdot x),$$

$$\mathcal S_{q,c}(u)=\sum_{a\bmod c}^{*}
\sum_{\substack{x\bmod qc\\q\mid F(x)}}
\xi_q(x)e_{qc}(aF(x)+u\cdot x).$$

Here `F(x)` is the actual integer matrix quadratic value. The definition
uses canonical representatives, and the proof shows that changing the
vector lift modulo `qc` or the unit lift modulo `c` does not change the
summand. For the unit lift, the condition `q ∣ F(x)` makes the phase
change divisible by `qc`. The identities `𝒮_{1,c}=S_c` and
`𝒮_{q,1}=C_q` therefore hold with the source normalization, including
`C_1=S_1=𝒮_{1,1}=1`.

For `q=q₁q₂`, `c=c₁c₂`, and `(q₁c₁,q₂c₂)=1`, the final theorem
proves

$$\mathcal S_{q,c}(u)=
\mathcal S_{q_1,c_1}(u)\mathcal S_{q_2,c_2}(u).$$

The checked bijections use the manuscript's scaled coordinates
`x=n₂x₁+n₁x₂` and `a=c₂a₁+c₁a₂`, where `n_i=q_i c_i`.
The proof splits the weight, the quadratic-congruence condition, and
the actual additive phase. It then reindexes the local unit parameters
by the source factors `c₂n₂` and `c₁n₁`. Primes may divide both `q`
and `c`; only the two CRT blocks must be coprime.

The second clause is the literal integer-frequency identity

$$\mathcal S_{q,c}(tu)=\mathcal S_{q,c}(u)
\qquad\text{when }\gcd(t,qc)=1.$$

Its proof reindexes the actual summation sets by `x↦t⁻¹x` and
`a↦t²a`. Negative integer scalars are included. At `qc=1`, the sum
is one and the gcd hypothesis also permits `t=0`; no separate
nonzero-integer assumption is added.

The source supplies `ξ_p` only at primes not dividing `N`.
`SourceWeights.lean` extends the family by zero elsewhere and proves
that every factor used when `(q,N)=1` is exactly an originally supplied
function. Thus `source_complete_sum_crt` imposes no hypothesis on an
excluded prime. Only the scalar invariance needed in the proof is used;
the source's weight-size and nondegeneracy assumptions are unnecessary
for these identities.

The supporting corollaries give

$$C_q(u)=\prod_{p\mid q}C_p(u)\quad(q\text{ squarefree}),\qquad
S_{c_1c_2}(u)=S_{c_1}(u)S_{c_2}(u)\quad((c_1,c_2)=1).$$

At a prime, a polynomial-character weight gives exactly the existing
`integralFourierSum`, with the same matrix, polynomial, frequency, and
standard additive character. This proves the connection to the checked
Section 4 estimates. The [source correspondence review](certification/correspondence/complete_sum_crt.md)
records both clauses and these definition bridges. All new exports use
only standard Lean foundations. The supporting corollaries do not
change the separate Pending status of auxiliary groups.

| Module | Checked contribution |
|---|---|
| [CompositeWeights](QuaternaryQuadraticForms/CompositeWeights.lean), [SourceWeights](QuaternaryQuadraticForms/SourceWeights.lean) | Actual prime-product weights, periodicity, scalar invariance, and exact extension of the source family |
| [CompleteSumAlgebra](QuaternaryQuadraticForms/CompleteSumAlgebra.lean), [CompleteSums](QuaternaryQuadraticForms/CompleteSums.lean) | Literal matrix quadratic value, integer lifts, complete sums, and representative independence |
| [CRTCharacters](QuaternaryQuadraticForms/CRTCharacters.lean), [CRTArithmetic](QuaternaryQuadraticForms/CRTArithmetic.lean) | Standard-character splitting and scaled CRT bijections on residues, units, and vectors |
| [MixedPhase](QuaternaryQuadraticForms/MixedPhase.lean) | Exact mixed phase identity and independence of the unit lift |
| [CompleteSumCRT](QuaternaryQuadraticForms/CompleteSumCRT.lean) | Full mixed-sum CRT factorization |
| [CompleteSumInvariance](QuaternaryQuadraticForms/CompleteSumInvariance.lean) | Invariance under the literal integer gcd condition |
| [CompleteSumSpecializations](QuaternaryQuadraticForms/CompleteSumSpecializations.lean) | Modulus-one identities and exact bridge to the previous prime Fourier sum |
| [CompleteSumFactorization](QuaternaryQuadraticForms/CompleteSumFactorization.lean) | Prime-factor product for squarefree `C_q` and multiplicativity of `S_c` |
| [CompleteSumTheorem](QuaternaryQuadraticForms/CompleteSumTheorem.lean) | Both clauses of Lemma 3.1 for the actual source family |

## Complete polynomial Fourier estimate

Lemma 4.4 is proved for the literal Fourier sum at every integral frequency.
For a homogeneous integral `G` of degree `n ≥ 2` satisfying the
characteristic-zero smoothness condition, a prime `p ∤ N_G`, and a
nonprincipal character with `ψ ^ n = 1`, the conclusion is

$$|C_p(u)|\le 2n^2\bigl(p^{3/2}+p^2
\mathbf 1_{D_p(\bar u)=0}\bigr),\qquad
C_p(0)=(p-1)a_p(G),$$

where $\bar u$ is the coordinatewise reduction of the integral frequency.
The theorem also includes the three weight conditions: value zero at the
origin, norm at most one everywhere, and invariance under every nonzero
scalar. These are proved for the actual function `x ↦ ψ(G(x))`.

The section count used for exceptional frequencies requires only `u ≠ 0`.
The hyperplane `u·x=0` has dimension three. If the nonsingular quadratic
form vanished on that entire plane, polarization in odd characteristic
would put the plane inside its orthogonal complement, whose dimension is
one. This contradiction proves that its restriction in three linear
coordinates is a nonzero polynomial of degree at most two. The proved
Schwartz–Zippel theorem in mathlib gives at most `2p²` affine zeros.
The actual projective-ray decomposition counts these zeros as
`1 + (p−1)M`, where `M` is the number of projective section points.
Since a good prime is at least three, this proves `M ≤ 2p+2`, including
tangent planes and singular sections. The character norm bound then gives
`|a_u| ≤ 2p+2` on every such section.

For `D_p(u) ≠ 0`, Lemma 4.1(ii) supplies the geometric hypotheses of
Lemma 4.3. Its section bound and the Katz bound for `a`, combined with
`C_p(u)=p a_u−a`, give the generic `2n²p^(3/2)` estimate. For a nonzero
exceptional frequency, the section count gives `2n²p²`. At the zero
frequency, the exact identity and the Katz bound give the same exceptional
estimate. The numerical comparisons, including the real power `p^(3/2)`,
are proved in Lean.

The terminal theorem `uniform_polynomial_fourier_bound` fixes `A,n` and
chooses `E ≥ 1` before `G` and `p`. Under the literal smoothness and
`p ∤ N_G` hypotheses, it then chooses `D_p ≠ 0` with degree at most `E`,
`D_p(0)=0`, and the dual-form and geometric transversality implications.
That same `D_p` works for every allowed character and every integral
frequency. No additional condition `p ∤ n` is imposed. The
[source correspondence review](certification/correspondence/fourier_rays.md)
matches all five conclusions and the quantifier order to the manuscript.

| Module | Checked contribution |
|---|---|
| [PlaneRestriction](QuaternaryQuadraticForms/PlaneRestriction.lean) | Nonvanishing of every nonzero plane's quadratic restriction and an actual ternary coordinate polynomial |
| [PolynomialGridCount](QuaternaryQuadraticForms/PolynomialGridCount.lean) | Schwartz–Zippel bound for the actual affine zero set of a nonzero ternary quadratic |
| [PlaneSectionCardinality](QuaternaryQuadraticForms/PlaneSectionCardinality.lean) | Exact affine-to-projective count, the bound `2p+2`, and the exceptional section-trace bound |
| [FourierBoundConstants](QuaternaryQuadraticForms/FourierBoundConstants.lean) | Generic, exceptional, and zero-frequency constant comparisons and the real-power identity |
| [FourierEstimates](QuaternaryQuadraticForms/FourierEstimates.lean) | Bounds for the literal Fourier sum from the exact ray identity and checked trace estimates |
| [FourierBound](QuaternaryQuadraticForms/FourierBound.lean) | Complete Lemma 4.4 for a supplied exceptional polynomial, under the literal integral hypotheses |
| [FourierTheorem](QuaternaryQuadraticForms/FourierTheorem.lean) | Uniform existence of the exceptional polynomial before the character, with all five conclusions |

## The diagonal bad-prime criterion

Lemma 4.5 is proved for the literal diagonal matrix polynomials

$$F(x)=\sum_{i=1}^4a_ix_i^2,\qquad
G(x)=\sum_{i=1}^4b_ix_i^2,\qquad
\alpha=\prod_{i=1}^4a_i,\qquad
M=\prod_{i<j}(a_ib_j-a_jb_i).$$

The source assumptions are `α ≠ 0` and nonvanishing of all six differences
with `i < j`. They imply the actual rank-two smoothness condition over
the algebraic closure of the rationals. For every prime `p ∤ N_F`, the
proved equivalence is

$$G\text{ has bad reduction at }p\quad\Longleftrightarrow\quad p\mid M.$$

The formal gradients have minors `4 x_i x_j (a_i b_j − a_j b_i)`.
If all pair differences are nonzero in the field, vanishing of these
minors forces at most one nonzero coordinate. Since each `a_i` is
nonzero, such a vector cannot satisfy `F(x)=0`. In the converse direction,
a vanishing pair difference supplies an actual point over the algebraic
closure with `x_i=1`, `x_j²=−a_i/a_j`, and all other coordinates zero.
The proof verifies both equations and dependence of the actual gradient
rows at that nonzero point.

Reduction and extension of the actual polynomials identify this field
criterion with `GoodReductionAt`. The prime criterion includes `p=3`
and allows zero coefficients `b_i`; it adds no condition `p ≥ 5`.
The integer coefficient product and `M` may have either sign.

Every additional bad prime divides the nonzero integer `M`, so finiteness
is proved directly, without Lang's elimination premise. More precisely,
the actual bad-prime finset consists of the prime factors of `|M|` outside
the prime factors of `N_F`. Taking their disjoint union proves

$$N_G=\operatorname{rad}(|2\alpha M|).$$

This is an equality for the existing `polynomialBadPrimeModulus`, valid
for every proof of finiteness passed to its definition. Primes dividing
both `N_F` and `M` occur once; no coprimality is assumed. All 24 new
supporting exports use only the standard Lean foundations. The
[source correspondence review](certification/correspondence/diagonal_bad_primes.md)
matches all three clauses to the manuscript.

| Module | Checked contribution |
|---|---|
| [DiagonalForms](QuaternaryQuadraticForms/DiagonalForms.lean) | Actual diagonal polynomial, six-factor product, coefficient maps, nonvanishing, and sign-compatible modulus identities |
| [DiagonalGeometry](QuaternaryQuadraticForms/DiagonalGeometry.lean) | Literal gradient minors, rank criterion, and the actual algebraic-closure singular point |
| [DiagonalReduction](QuaternaryQuadraticForms/DiagonalReduction.lean) | Characteristic-zero smoothness and exact geometric bad reduction after coefficient reduction and extension |
| [BadPrimeRadical](QuaternaryQuadraticForms/BadPrimeRadical.lean) | Direct finiteness, exact additional-prime finset, and radical equality for the existing modulus |
| [DiagonalBadPrimes](QuaternaryQuadraticForms/DiagonalBadPrimes.lean) | Complete Lemma 4.5, including the exact modulus for every finiteness proof |

## The exact diagonal pencil formula

For the source's integral diagonal coefficients, Lemma 4.6 uses the
literal prime restriction `p ∤ 2αM`. It defines the four distinct
singular parameters `t_i = −b_i/a_i` in the prime field and the actual
pencil data

$$\kappa_i=-a_i\prod_{j\ne i}(a_i b_j-a_j b_i),\qquad
\Phi_u(t)=\sum_i u_i^2\prod_{j\ne i}(b_j+t a_j),$$

$$\nu_i(u)=\sum_{j\ne i}u_j^2
\prod_{\ell\ne i,j}(a_i b_\ell-a_\ell b_i).$$

The final theorem `diagonal_pencil` proves all three clauses for the
existing `integralFourierSum` and `integralProjectiveQuadraticTrace`.
The exact formula is

$$C_p(u)=p\sum_{t\notin\{t_1,t_2,t_3,t_4\}}
\chi_p(-\Phi_u(t))+
 p\sum_{i:\,p\mid u_i}\chi_p(\kappa_i)R_p(\nu_i(u)),$$

where the actual prime Ramanujan sum is `p−1` at zero and `−1`
elsewhere. In particular, the singular terms with `ν_i(u)=0` are
retained; they can have size `p(p−1)`.

The shared one-dimensional Gauss identities are proved from mathlib's
Gauss-sum and square-root counting theorems for the actual quadratic
character and standard additive character. They include inversion at
zero, `τ_p² = χ_p(−1)p`, `τ_p⁴ = p²`, and both branches of square
completion. Character orthogonality and the finite-product decomposition
then give the actual Fourier expansion. The parameter change takes place
over nonzero units, so inversion never uses the zero Gauss parameter.

At a singular parameter, the checked identities are
`−Δ_i = κ_i/a_i⁴` and `w_i = ν_i/(a_i²Δ_i)`. The second denominator
is a unit, which preserves the Ramanujan value. At zero frequency, the
regular sum vanishes and the existing identity `C_p(0)=(p−1)a_p(G)`
gives the literal integer equality

$$a_p(G)=p\sum_i\chi_p(\kappa_i).$$

For `p ∤ F*(u)u₁u₂u₃u₄`, every singular term vanishes. The formal
polynomial `Φ_u` has degree three because its leading coefficient is
the actual adjugate quadratic value `F*(u)`. The four distinct singular
parameters imply `p ≥ 5`. The cubic character sum has norm at most
`2√p`: the separable case uses the registered Weil estimate, while the
repeated-root cases are proved internally. Deleting the four parameters
therefore gives

$$|C_p(u)|\le 2p^{3/2}+4p.$$

The [source correspondence review](certification/correspondence/diagonal_pencil.md)
tracks signs, normalization, singular terms, the zero-frequency trace,
coefficient reduction, and the generic divisibility condition. The
exact formula and trace introduce no external premise; the generic
bound adds only the already registered Weil premise. The global
asymptotic in Theorem 1.3 remains Pending.

| Module | Checked contribution |
|---|---|
| [PrimeQuadraticGauss](QuaternaryQuadraticForms/PrimeQuadraticGauss.lean) | Actual prime Gauss identities, inversion, and both square-completion branches |
| [PrimeRamanujan](QuaternaryQuadraticForms/PrimeRamanujan.lean) | Actual prime Ramanujan values and invariance under unit multiplication |
| [DiagonalPencil](QuaternaryQuadraticForms/DiagonalPencil.lean), [DiagonalPencilCubic](QuaternaryQuadraticForms/DiagonalPencilCubic.lean), [DiagonalPencilAlgebra](QuaternaryQuadraticForms/DiagonalPencilAlgebra.lean) | Literal source data, coefficient maps, dual leading coefficient, distinct roots, and regular/singular algebra |
| [FourierOrthogonality](QuaternaryQuadraticForms/FourierOrthogonality.lean), [FourierGaussExpansion](QuaternaryQuadraticForms/FourierGaussExpansion.lean) | Actual finite Fourier expansion from orthogonality and Gauss inversion |
| [DiagonalPencilEvaluation](QuaternaryQuadraticForms/DiagonalPencilEvaluation.lean) | Exact contributions of each regular and singular member |
| [DiagonalPencilFormula](QuaternaryQuadraticForms/DiagonalPencilFormula.lean) | Complete finite-field Fourier pencil identity |
| [CubicCharacterSum](QuaternaryQuadraticForms/CubicCharacterSum.lean) | Cubic estimates with separable and repeated-root cases, including deletion of four parameters |
| [DiagonalPencilConsequences](QuaternaryQuadraticForms/DiagonalPencilConsequences.lean) | Actual complex/integer projective trace and generic Fourier bound |
| [DiagonalPencilReduction](QuaternaryQuadraticForms/DiagonalPencilReduction.lean), [DiagonalPencilTheorem](QuaternaryQuadraticForms/DiagonalPencilTheorem.lean) | Literal integral hypotheses and all clauses of Lemma 4.6 |

## Bad primes and the uniform coefficient-height bound

Lemma 4.1(i) is proved for the actual characteristic-zero rank condition,
the intrinsic set of bad primes outside `N_F`, and the manuscript's height
`H_G = max(2, max |coefficient of G|)`. For fixed `F,n`, the result chooses
positive integers `C,K` before quantifying over `G` and proves

$$N_G\le K H_G^C.$$

The formal system consists of `F`, `G`, and all sixteen ordered two-by-two
gradient minors. The zero and repeated minors preserve the common zero
locus of the manuscript's six minors. The rank criterion, homogeneous
degrees, and compatibility with coefficient reduction are proved.

Lang's general theorem supplies a finite family in independent generic
coefficients. The certificate substitutes the actual coefficient
polynomials into that family and proves that specialization commutes with
evaluation. This gives one fixed integer family `R_j` in the coefficients
of `G`, valid in characteristic zero and at every prime. Smoothness selects
a nonzero integer `z = R_j(coeff G)`; every bad prime divides that same
integer. Their distinct-prime product therefore divides `|z|`.

The elementary polynomial estimate
`|P(x)| ≤ (sum of absolute coefficients of P) H^(total degree of P)`
for `H ≥ 1` and `|x_i| ≤ H` gives uniform constants for this finite family. Thus
`N_G ≤ rad(N_F) |z| ≤ K H_G^C`, with the fixed radical absorbed into `K`.
The proof bounds the original modulus; it does not replace its bad-prime
set with all prime divisors of the chosen resultant value.

| Module | Checked contribution |
|---|---|
| [HomogeneousForms](QuaternaryQuadraticForms/HomogeneousForms.lean), [EliminationData](QuaternaryQuadraticForms/EliminationData.lean) | Finite coefficient vectors, reconstruction of literal forms, and nonzero geometric zeros |
| [Trusted/Elimination](QuaternaryQuadraticForms/Trusted/Elimination.lean), [EliminationFamily](QuaternaryQuadraticForms/EliminationFamily.lean) | The registered general Lang input and the internally proved substitution of polynomial parameters |
| [RankMinors](QuaternaryQuadraticForms/RankMinors.lean), [BadReductionSystem](QuaternaryQuadraticForms/BadReductionSystem.lean) | The exact rank-failure equations, assigned homogeneous degrees, and coefficient-map identities |
| [GenericQuadricFamily](QuaternaryQuadraticForms/GenericQuadricFamily.lean), [GeometricReduction](QuaternaryQuadraticForms/GeometricReduction.lean) | The fixed generic family and its identification with the characteristic-zero and prime-field rank conditions |
| [BadReductionResultants](QuaternaryQuadraticForms/BadReductionResultants.lean) | One fixed integer family, the nonzero common-divisor witness, and finiteness of the actual bad-prime set |
| [PolynomialHeight](QuaternaryQuadraticForms/PolynomialHeight.lean), [BadReductionHeight](QuaternaryQuadraticForms/BadReductionHeight.lean) | Uniform polynomial evaluation bounds and complete Lemma 4.1(i) for the literal `N_G` |

The [correspondence review](certification/correspondence/bad_reduction.md)
records the constants' quantifier order. The exceptional-plane construction
completing part (ii) is described next.

## The exceptional-plane polynomial

Lemma 4.1(ii) is proved for every good prime under the manuscript's literal
`p ∤ N_G` hypothesis. For fixed `F,n`, it chooses `E ≥ 1` before `G` and `p`
and constructs

$$D_p\in\mathbf F_p[u_1,u_2,u_3,u_4],\qquad
D_p\ne0,\qquad\deg D_p\le E,\qquad D_p(0)=0.$$

Whenever `D_p(u) ≠ 0`, the proof gives `F*(u) ≠ 0` and rank three of
`∇F(x), ∇G(x), u` at every nonzero geometric solution of
`F(x)=G(x)=u·x=0`.

The second elimination system contains the actual equations `F,G,u·x`
and their three-by-three gradient minors. The implementation retains all
64 ordered column triples; the checked minor criterion identifies their
common zero locus with failure of the literal rank-three condition.
Together with the three equations, this gives 67 homogeneous forms of
assigned degrees `2,n,1,n,…,n`, including zero specializations.

Lang's existing general input produces one finite family of integral
polynomials `R_j(g,u)` in the coefficients of `G` and the plane normal.
The family is chosen before the field and the parameter assignment.
The general Bertini input supplies a transverse plane over the algebraic
closure. Internal linear algebra proves its rank-three condition, so one
resultant has nonzero evaluation there. Compatibility of partial
specialization with coefficient extension proves that the corresponding
`S(u)=R_j(G,u)` is already a nonzero polynomial over the prime field.
No prime-field transverse-plane witness is required.

Partial specialization does not increase total degree. Thus
`E = 2 + sup_j totalDegree(R_j)` is uniform in the form and the prime;
the finite supremum is zero for an empty family.
The final construction is the literal product `D_p = F* S`.
Nonsingularity and odd characteristic prove that the dual quadratic
polynomial is nonzero. Its degree and zero constant term give the stated
degree bound and `D_p(0)=0`; the two factors give the dual-form and
transversality implications.

| Module | Checked contribution |
|---|---|
| [RankThreeMinors](QuaternaryQuadraticForms/RankThreeMinors.lean), [PlaneReductionSystem](QuaternaryQuadraticForms/PlaneReductionSystem.lean) | Literal rank-three minors, second homogeneous system, and its geometric zero locus |
| [ExceptionalPlaneResultants](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean) | One fixed integral family in the form coefficients and normal, valid over every field |
| [PlaneResultantSpecialization](QuaternaryQuadraticForms/PlaneResultantSpecialization.lean) | Reflection of geometric zeros over an algebraically closed field and compatibility with coefficient extension |
| [Trusted/Bertini](QuaternaryQuadraticForms/Trusted/Bertini.lean), [BertiniPlane](QuaternaryQuadraticForms/BertiniPlane.lean) | Registered general tangent interface and the internally proved rank-three specialization |
| [ParameterSpecialization](QuaternaryQuadraticForms/ParameterSpecialization.lean), [ExceptionalPlaneDegree](QuaternaryQuadraticForms/ExceptionalPlaneDegree.lean) | Degree bound under partial parameter specialization |
| [ExceptionalPlanePolynomial](QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean) | Complete Lemma 4.1(ii), including quantifier order, nonvanishing, degree, and geometric implications |

## Complete quadratic trace theorem

Under the manuscript's characteristic-zero smoothness hypothesis, for a
quadratic homogeneous `G` and a prime `p ∤ N_G`, the checked theorem proves

$$a_p(G)\in\mathbb Z,\qquad p\mid a_p(G),\qquad |a_p(G)|\le4p.$$

The trace is first constructed as an integer sum of quadratic-character
values, then its complex cast is identified with the projective trace already
used in the Fourier identities. Euler's criterion and mathlib's polynomial-sum
vanishing theorem show that the affine trace is zero modulo `p`. The checked
identity `C_p(0) = (p-1)a_p(G)` then gives projective divisibility.

This divisibility argument needs neither nonsingularity nor smoothness.
The degree-two Katz specialization supplies the size bound under good
reduction. The final theorem in
[QuadraticTraceTheorem.lean](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean)
starts from the manuscript's symmetric nonsingular integral matrix,
quadratic homogeneity, characteristic-zero smoothness, and `p ∤ N_G`.
It constructs the finiteness proof from smoothness and derives
`p ∤ N_F` and the geometric good-reduction condition from the exact modulus.
No separate finiteness or good-reduction assumption remains. The conclusion
identifies the literal complex projective trace with an integer having
the stated divisibility and bound.
The [correspondence review](certification/correspondence/quadratic_trace.md)
records the complete source statement and the actual integer and complex
exports. This theorem uses the registered Lang and Katz inputs; it does not
use the separate Weil premise.

## Reproduce the checks

The project pins official Lean 4.24.0 and official mathlib4 commit
f897ebcf72cd16f89ab4577d0c826cd14afaafc7, matching the established model projects.
The complete transitive dependency lock is committed.

With the official Lean toolchain manager and Python 3 available:

    lake exe cache get \
      Mathlib.Algebra.BigOperators.Group.Finset.Sigma \
      Mathlib.Algebra.BigOperators.Intervals \
      Mathlib.Algebra.BigOperators.Module \
      Mathlib.Algebra.BigOperators.Ring.Finset \
      Mathlib.Algebra.Field.ZMod \
      Mathlib.Algebra.Group.Units.Equiv \
      Mathlib.Algebra.MvPolynomial.Degrees \
      Mathlib.Algebra.MvPolynomial.Equiv \
      Mathlib.Algebra.MvPolynomial.Eval \
      Mathlib.Algebra.MvPolynomial.PDeriv \
      Mathlib.Algebra.MvPolynomial.SchwartzZippel \
      Mathlib.Algebra.MvPolynomial.Variables \
      Mathlib.Algebra.Order.BigOperators.Group.Finset \
      Mathlib.Algebra.Order.BigOperators.Ring.Finset \
      Mathlib.Algebra.Order.Floor.Ring \
      Mathlib.Algebra.Order.Ring.Pow \
      Mathlib.Algebra.Polynomial.BigOperators \
      Mathlib.Algebra.Polynomial.Coeff \
      Mathlib.Algebra.Polynomial.Degree.Lemmas \
      Mathlib.Algebra.Polynomial.Homogenize \
      Mathlib.Algebra.Polynomial.Roots \
      Mathlib.Algebra.Ring.Periodic \
      Mathlib.Algebra.Star.BigOperators \
      Mathlib.Analysis.Calculus.ContDiff.Basic \
      Mathlib.Analysis.Calculus.ContDiff.Bounds \
      Mathlib.Analysis.Calculus.ContDiff.WithLp \
      Mathlib.Analysis.Calculus.Deriv.Basic \
      Mathlib.Analysis.Calculus.FDeriv.Add \
      Mathlib.Analysis.Calculus.FDeriv.Measurable \
      Mathlib.Analysis.Calculus.Gradient.Basic \
      Mathlib.Analysis.Calculus.IteratedDeriv.Defs \
      Mathlib.Analysis.Complex.Basic \
      Mathlib.Analysis.InnerProductSpace.Calculus \
      Mathlib.Analysis.InnerProductSpace.PiL2 \
      Mathlib.Analysis.Normed.Group.Bounded \
      Mathlib.Analysis.Normed.Group.FunctionSeries \
      Mathlib.Analysis.Normed.Module.FiniteDimension \
      Mathlib.Analysis.PSeries \
      Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar \
      Mathlib.Analysis.SpecialFunctions.Log.Base \
      Mathlib.Analysis.SpecialFunctions.Log.Summable \
      Mathlib.Analysis.SpecialFunctions.Pow.Continuity \
      Mathlib.Analysis.SpecialFunctions.Pow.NNReal \
      Mathlib.Analysis.SpecialFunctions.Pow.Real \
      Mathlib.Analysis.SpecialFunctions.SmoothTransition \
      Mathlib.Analysis.SpecialFunctions.Sqrt \
      Mathlib.Analysis.SpecificLimits.Basic \
      Mathlib.Analysis.SpecificLimits.Normed \
      Mathlib.Data.Fin.Tuple.Finset \
      Mathlib.Data.Fin.VecNotation \
      Mathlib.Data.Finset.Max \
      Mathlib.Data.Finset.Prod \
      Mathlib.Data.Finsupp.Weight \
      Mathlib.Data.Fintype.BigOperators \
      Mathlib.Data.Fintype.Perm \
      Mathlib.Data.Int.Interval \
      Mathlib.Data.Int.ModEq \
      Mathlib.Data.Matrix.Mul \
      Mathlib.Data.Nat.Factorization.Basic \
      Mathlib.Data.Nat.Factorization.Defs \
      Mathlib.Data.Nat.Factorization.Induction \
      Mathlib.Data.Nat.GCD.Basic \
      Mathlib.Data.Nat.GCD.BigOperators \
      Mathlib.Data.Nat.Prime.Basic \
      Mathlib.Data.Nat.PrimeFin \
      Mathlib.Data.Nat.Squarefree \
      Mathlib.Data.Nat.Totient \
      Mathlib.Data.PNat.Basic \
      Mathlib.Data.PNat.Interval \
      Mathlib.Data.Real.Archimedean \
      Mathlib.Data.Real.Basic \
      Mathlib.Data.Real.Sqrt \
      Mathlib.Data.Set.Card \
      Mathlib.Data.ZMod.Basic \
      Mathlib.Data.ZMod.Coprime \
      Mathlib.FieldTheory.ChevalleyWarning \
      Mathlib.FieldTheory.Finite.Basic \
      Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure \
      Mathlib.FieldTheory.IsAlgClosed.Basic \
      Mathlib.FieldTheory.Perfect \
      Mathlib.GroupTheory.Index \
      Mathlib.LinearAlgebra.Basis.VectorSpace \
      Mathlib.LinearAlgebra.BilinearForm.Orthogonal \
      Mathlib.LinearAlgebra.Dual.Lemmas \
      Mathlib.LinearAlgebra.FiniteDimensional.Lemmas \
      Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient \
      Mathlib.LinearAlgebra.LinearIndependent.Basic \
      Mathlib.LinearAlgebra.LinearIndependent.Lemmas \
      Mathlib.LinearAlgebra.Matrix.Adjugate \
      Mathlib.LinearAlgebra.Matrix.BilinearForm \
      Mathlib.LinearAlgebra.Matrix.Determinant.Basic \
      Mathlib.LinearAlgebra.Matrix.Dual \
      Mathlib.LinearAlgebra.Matrix.Hermitian \
      Mathlib.LinearAlgebra.Matrix.NonsingularInverse \
      Mathlib.LinearAlgebra.Matrix.Rank \
      Mathlib.LinearAlgebra.Matrix.ToLin \
      Mathlib.LinearAlgebra.Multilinear.Basis \
      Mathlib.LinearAlgebra.Projectivization.Cardinality \
      Mathlib.LinearAlgebra.QuadraticForm.Basic \
      Mathlib.Logic.Equiv.Fin.Basic \
      Mathlib.Logic.Equiv.Prod \
      Mathlib.MeasureTheory.Constructions.Polish.Basic \
      Mathlib.MeasureTheory.Group.Integral \
      Mathlib.MeasureTheory.Integral.Bochner.Basic \
      Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap \
      Mathlib.MeasureTheory.Integral.Bochner.Set \
      Mathlib.MeasureTheory.Integral.Pi \
      Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace \
      Mathlib.MeasureTheory.Measure.Haar.NormedSpace \
      Mathlib.MeasureTheory.Measure.Hausdorff \
      Mathlib.MeasureTheory.Measure.WithDensity \
      Mathlib.NumberTheory.ArithmeticFunction \
      Mathlib.NumberTheory.DirichletCharacter.Basic \
      Mathlib.NumberTheory.DirichletCharacter.Bounds \
      Mathlib.NumberTheory.Divisors \
      Mathlib.NumberTheory.EulerProduct.Basic \
      Mathlib.NumberTheory.GaussSum \
      Mathlib.NumberTheory.Harmonic.Bounds \
      Mathlib.NumberTheory.LSeries.Dirichlet \
      Mathlib.NumberTheory.LSeries.DirichletContinuation \
      Mathlib.NumberTheory.LSeries.SumCoeff \
      Mathlib.NumberTheory.LegendreSymbol.Basic \
      Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol \
      Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic \
      Mathlib.Order.Interval.Set.OrdConnected \
      Mathlib.RingTheory.Localization.FractionRing \
      Mathlib.RingTheory.Localization.Integer \
      Mathlib.RingTheory.MvPolynomial.EulerIdentity \
      Mathlib.RingTheory.MvPolynomial.Homogeneous \
      Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex \
      Mathlib.Tactic.FieldSimp \
      Mathlib.Tactic.FinCases \
      Mathlib.Tactic.GCongr \
      Mathlib.Tactic.IntervalCases \
      Mathlib.Tactic.Linarith \
      Mathlib.Tactic.LinearCombination \
      Mathlib.Tactic.NormNum \
      Mathlib.Tactic.Positivity \
      Mathlib.Tactic.Ring \
      Mathlib.Topology.Algebra.InfiniteSum.Constructions \
      Mathlib.Topology.Algebra.InfiniteSum.NatInt \
      Mathlib.Topology.Algebra.InfiniteSum.Order \
      Mathlib.Topology.Algebra.InfiniteSum.Ring \
      Mathlib.Topology.Instances.Real.Lemmas \
      Mathlib.Topology.Order.Basic \
      Mathlib.Topology.Order.Compact
    python3 scripts/verify_certificate.py

The verifier checks the frozen source, every inventory entry, the dependency
graph, toolchain and dependency revisions, local proof modules, actual theorem
types, and axiom dependencies. GitHub Actions runs the same verifier and
publishes its JSON report.

To regenerate the readable inventory and graphs:

    python3 scripts/render_inventory.py
    python3 scripts/build_dependency_graph.py

Graph rendering requires Graphviz. It is not needed to check the Lean proofs.

## Continuation status

The requested **Lemma 5.1** is complete at the proof and source-review level.
The current verification block tracks its execution gates. This session
stops after Lemma 5.1; no further proof target is automatically selected.

The numbered inventory is **26 Complete, 0 Partial, 0 Active, 16 Pending**.
All Section 2 results, Lemmas 3.1–3.11, all Section 4 lemmas, and Lemmas
5.1 and 5.9 are complete. Supplementary groups remain **5 Certified,
28 Pending**. **Proposition 5.1 remains Pending**, together with the separate
scaled-integral obligation `aux:Ipiece`, weighted cone count `aux:conecount`,
and absolute singular-integral convergence for weights whose support
contains the origin. These are later analytic obligations, not prerequisites
for the completed delta–Poisson lemma. The whole paper is not certified.
