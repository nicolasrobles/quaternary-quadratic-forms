# Character sums over zeros of quaternary quadratic forms

Source-relative Lean verification of the paper by Hemjyoti Nath, Nicolas Robles,
and Alexandru Zaharescu.

The mathematical source is the audited frozen manuscript
[quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).
The associated [34-page PDF](manuscript/quadratic_character_sums_github.pdf) is
included. The source SHA-256 is

    d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33

## Current status

**Complete: 12 · Partial: 0 · Active: 0 · Pending: 30** — 42 numbered results.

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

The current scope covers 536 theorem exports across 112 Lean modules,
four unchanged separately registered external Lean premises, and 20 mapped
source groups. All 33 auxiliary/supplementary groups remain Pending.
This repository does not yet provide a certificate for the whole paper.

The Lemma 3.2 milestone adds 54 public theorem exports in 16 new
modules, with 137 recorded input hashes including the new
correspondence review.

**The full local aggregate verifier passed for all 536 theorem exports
and 112 Lean modules.** All 137 input hashes match the checked files.
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

The [local verification report](certification/verification_report.json)
contains 780,870 bytes and has SHA-256
`824069fc67d6f55812e9c9928c1461bb580564b92ee0f7e4cf1b252e59cd0699`.
It records 12 Certified, zero Partial or Active, and 30 Pending numbered
results; all 33 auxiliary/supplementary groups remain Pending.

**GitHub CI for this 536-export scope is pending.** The successful
GitHub runs below cover their stated earlier scopes. The
[execution checkpoint](CHECKPOINT.md) records the new local result
and its exact comparison with the preceding 482-export report.

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
      Mathlib.Algebra.BigOperators.Ring.Finset \
      Mathlib.Tactic.Ring \
      Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar \
      Mathlib.Data.Fintype.BigOperators \
      Mathlib.LinearAlgebra.Projectivization.Cardinality \
      Mathlib.Analysis.Complex.Basic \
      Mathlib.NumberTheory.DirichletCharacter.Bounds \
      Mathlib.NumberTheory.GaussSum \
      Mathlib.FieldTheory.Perfect \
      Mathlib.Algebra.Polynomial.BigOperators \
      Mathlib.RingTheory.MvPolynomial.Homogeneous \
      Mathlib.Data.Matrix.Mul \
      Mathlib.FieldTheory.ChevalleyWarning \
      Mathlib.NumberTheory.LegendreSymbol.Basic \
      Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic \
      Mathlib.Algebra.Polynomial.Homogenize \
      Mathlib.Data.Fin.VecNotation \
      Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure \
      Mathlib.Algebra.MvPolynomial.PDeriv \
      Mathlib.LinearAlgebra.Basis.VectorSpace \
      Mathlib.LinearAlgebra.BilinearForm.Orthogonal \
      Mathlib.LinearAlgebra.Dual.Lemmas \
      Mathlib.LinearAlgebra.FiniteDimensional.Lemmas \
      Mathlib.LinearAlgebra.LinearIndependent.Basic \
      Mathlib.LinearAlgebra.LinearIndependent.Lemmas \
      Mathlib.LinearAlgebra.Matrix.Adjugate \
      Mathlib.LinearAlgebra.Matrix.BilinearForm \
      Mathlib.LinearAlgebra.Matrix.Dual \
      Mathlib.LinearAlgebra.Matrix.Rank \
      Mathlib.LinearAlgebra.QuadraticForm.Basic \
      Mathlib.RingTheory.MvPolynomial.EulerIdentity \
      Mathlib.Tactic.FieldSimp \
      Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex \
      Mathlib.Data.Nat.Factorization.Basic \
      Mathlib.Data.Nat.PrimeFin \
      Mathlib.Data.Nat.Squarefree \
      Mathlib.Data.ZMod.Coprime \
      Mathlib.Algebra.Group.Units.Equiv \
      Mathlib.Logic.Equiv.Prod \
      Mathlib.Logic.Equiv.Fin.Basic \
      Mathlib.Algebra.Polynomial.Coeff \
      Mathlib.Algebra.MvPolynomial.Eval \
      Mathlib.Algebra.MvPolynomial.Degrees \
      Mathlib.Algebra.MvPolynomial.Variables \
      Mathlib.Algebra.MvPolynomial.SchwartzZippel \
      Mathlib.FieldTheory.Finite.Basic \
      Mathlib.Analysis.SpecialFunctions.Pow.Real \
      Mathlib.Algebra.Order.BigOperators.Group.Finset \
      Mathlib.Data.Finsupp.Weight \
      Mathlib.Tactic.IntervalCases \
      Mathlib.Tactic.FinCases \
      Mathlib.Tactic.LinearCombination \
      Mathlib.Tactic.Linarith \
      Mathlib.Tactic.NormNum
    python3 scripts/verify_certificate.py

The verifier checks the frozen source, every inventory entry, the dependency
graph, toolchain and dependency revisions, local proof modules, actual theorem
types, and axiom dependencies. GitHub Actions runs the same verifier and
publishes its JSON report.

To regenerate the readable inventory and graphs:

    python3 scripts/render_inventory.py
    python3 scripts/build_dependency_graph.py

Graph rendering requires Graphviz. It is not needed to check the Lean proofs.

## Next proof branch

The next bounded target is complete Lemma 3.3, source lines 1156–1178.
For the source's nonsingular symmetric integral matrix, every integer
modulus $c\ge1$, and every integral frequency $u$, it asserts

$$|S_c(u)|\le4\sqrt{|\det A|}\,c^3.$$

The proof must start with the squared norm of the actual Gauss sum,
use additive orthogonality to bound it by $c^4$ times the number of
solutions to $2Az=0\pmod c$, and prove that this kernel has at most
$16|\det A|$ elements. The source's Smith normal-form argument gives
the exact kernel count $\prod_i\gcd(d_i,c)$, where the invariant
factors of `2A` have product $16|\det A|$. Taking square roots and
summing over the actual unit parameters then gives the full bound.
This target includes modulus one and all bad-prime factors; it remains
Pending.

Lemmas 3.1 and 3.2 and all Section 4 lemmas are complete. The global
asymptotic in Theorem 1.3, the analytic assembly, and Theorems 1.1 and
1.4 remain Pending. All 33 auxiliary/supplementary groups remain
Pending.
