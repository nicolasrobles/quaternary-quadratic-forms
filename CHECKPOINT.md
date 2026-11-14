# Katz estimate and quadratic-trace checkpoint

## Numbered-result status

Complete: **5**. Partial: **2**. Active numbered targets: **0**.
Pending: **35**. All 33 auxiliary/supplementary groups remain Pending.

**Lemma 2.5 and Corollary 2.6 are Certified relative to the accepted literature
inputs.** The first is matched to the cited simple-root univariate Weil bound.
The second is proved under the literal manuscript hypotheses, with the
projective charts, affine polynomial, degree, and geometric-root deductions
checked in Lean.

**Lemmas 4.2 and 4.3 are now Certified.** The conic parametrization uses one tuple of actual binary quadratic
forms over every field extension. The plane-section estimate uses the literal
geometric rank-three hypothesis and the actual projective character sum.
Their earlier local and GitHub verification evidence is preserved below.

**Lemma 2.7 is now Certified.**
The new Katz milestone includes the literal quadric geometry, the exact
coefficient, and the scalar bound. The full local verifier passed. GitHub
Actions verification also passed at the exact proof commit recorded below.

Lemma 4.4 retains its checked weight properties, ray identity (4.5), and exact
zero-frequency clause; its pointwise estimate remains pending. Lemma 5.9
retains its checked integrality and divisibility clauses and now has the
size bound |a_p(G)| ≤ 4p under literal good reduction. Its `N_G` wrappers
require an explicit proof that the bad-prime set is finite; deriving that
proof from characteristic-zero smoothness is still pending. Both numbered
results remain Partial.

## Mathematical scope

### Katz input and quadric specialization

The new external declaration is
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

### Quadratic trace and the remaining reduction deduction

`QuadraticTraceBound.lean` specializes the new estimate to degree two and
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

The pending step is to derive such a nonzero witness from the manuscript's
characteristic-zero rank condition using the elimination argument in
Lemma 4.1(i). The explicit finiteness argument has not been discharged by an
axiom or replaced by an arbitrary modulus. Consequently the frozen
Lemma 5.9 remains Partial despite completion of its finite-field size
estimate and the conditional literal-modulus wrappers.

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

## Current verification

The current milestone covers 207 theorem exports across 38 project Lean
modules, 56 verification input hashes, 19 mapped source groups, and two
separately registered external Lean premises. The latter are the existing
Weil input and the new composite Katz/Fulton spectral input. Source groups
and Lean premise declarations are counted separately.

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

All 56 input hashes match the verified files, including eight correspondence
records. Independent source reviews found no missing clause or strengthened
hypothesis in Lemma 2.7. The actual types of the final Lemma 5.9 wrappers
retain their explicit finite-set argument, as recorded in the Partial status.
The new metadata checks also rejected a composite registration with an omitted
source component and one whose secondary source did not register the declaration.

- [Local verification report](certification/verification_report.json).
- Lean: official 4.24.0.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Manuscript SHA-256: `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

### Current GitHub execution

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
match the local verified files, including the eight correspondence reviews.
All 207 theorem records, both separately inspected literature-input records,
and the pinned dependency revisions match the local report. The CI report
records five Certified, two Partial, and 35 Pending numbered results; it
explicitly leaves whole-paper certification false.

The subsequent evidence commit changes only README, this checkpoint, and the
preserved CI JSON and ZIP. The Lean sources, verifier, statement ledger, and
correspondence records remain identical to the checked proof commit.

The actual quadric geometry, coefficient calculation, finite-sum inequality,
and good-reduction arithmetic introduce no further external premises.
The new Katz bound and quadratic-trace size exports use the new spectral
input; they do not depend on the separate Weil estimate.

## Earlier checked checkpoints

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

## Next target

Prove the elimination witness in Lemma 4.1(i): the characteristic-zero
smoothness hypothesis must yield a nonzero integer `P_i(G)` divisible by
every bad prime. The existing arithmetic bridge then supplies the actual
finite bad-prime set and closes the remaining reduction dependency in
Lemma 5.9.

The next source interface has been scoped against Lang, *Algebra*, revised
third edition: IX.4.1, printed p. 402, gives a finite resultant system over
the integers; IX.3.2, p. 390, and the remarks after IX.3.1, p. 389, fix its
arbitrary-field and algebraic-closure interpretation. The finite family is
chosen before the field and coefficient specialization. Specialization may
produce zero polynomials, and no degree/characteristic coprimality restriction
is needed. No Lean elimination premise has yet been introduced.

The internal application uses the eight homogeneous forms consisting of
`F`, `G`, and the six two-by-two gradient minors, with assigned degrees
`2,n,n,n,n,n,n,n`. Rank failure, coefficient reduction, the nonzero
characteristic-zero resultant value, and divisibility at every bad prime
must all be proved internally.

The coefficient-height estimate in Lemma 4.1(i), the exceptional-plane
polynomial in Lemma 4.1(ii), the exceptional-section count, and the final
Fourier-bound assembly remain further obligations. The proved Katz and
plane-section bounds and the exact ray identity are available for that work.
