# Bad-reduction, height, and quadratic-trace checkpoint

## Numbered-result status

Complete: **6**. Partial: **2**. Active numbered targets: **0**.
Pending: **34**. All 33 auxiliary/supplementary groups remain Pending.

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

**Lemma 5.9 is now Certified.** Its final integer and complex trace theorems
derive finiteness of the actual bad-prime set from characteristic-zero
smoothness, then use the literal `p ∤ N_G` hypothesis to prove integrality,
divisibility by `p`, and the bound `|a_p(G)| ≤ 4p`. No separate finiteness
or good-reduction hypothesis remains.

**Lemma 4.1(i) is complete.** Its finite bad-prime set and bound
`N_G ≤ K H_G^C` are proved with constants fixed before `G`. Lemma 4.1 is
Partial because part (ii), the exceptional-plane polynomial, remains
pending. Lemma 4.4 also remains Partial: its weight properties, ray
identity (4.5), and exact zero-frequency clause are checked, while its
pointwise estimate remains pending. Theorems 1.1 and 1.4 remain Pending.

## Mathematical scope

### Lang input and the actual bad-reduction system

The new external declaration is
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
covers all of part (i). Part (ii), including the exceptional-plane
polynomial and its uniform degree, remains pending. This checkpoint makes
no completion claim for the whole two-part Lemma 4.1.

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

- [Complete Lemma 4.1(i)](QuaternaryQuadraticForms/BadReductionHeight.lean).
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

## Current verification

The current milestone registers 261 theorem exports across 50 project
Lean modules, 70 verification input hashes, 19 mapped source groups, and
three separately registered external Lean premises. They are the Weil
input, the composite Katz/Fulton spectral input, and the general Lang
resultant input. Source groups and Lean premise declarations are counted
separately.

The new modules have passed strict builds under official Lean 4.24.0 and
the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. Independent source reviews cover the exact Lang
interface, the full content of Lemma 4.1(i), and completion of Lemma 5.9.
The frozen manuscript and PDF are unchanged.

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

All 70 input hashes match the verified files, including ten correspondence
records. The full Lemma 4.1(i) export places the positive constants before
the form G. The final Lemma 5.9 types contain no separately assumed
finiteness or good-reduction condition. Source review found no missing
clause or strengthened hypothesis in these completed statements.

- [Local verification report](certification/verification_report.json).
- Lean: official 4.24.0.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Manuscript SHA-256: `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

### Current GitHub execution

Publication and GitHub Actions verification for this checkpoint are pending.
The successful runs below are retained as evidence for their earlier scopes.

## Earlier checked checkpoints

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

## Next target

Complete Lemma 4.1(ii): for every good prime, construct a nonzero
`D_p` with `D_p(0)=0` and degree bounded only in terms of `F,n`. Its
nonvanishing must imply `F*(u)≠0` and rank three for the actual rows
`∇F(x), ∇G(x), u` at every nonzero geometric common zero.

This requires the second homogeneous elimination system, involving the
plane equation and the three-by-three minors, together with the exact
cited geometric input that supplies a transverse plane over the algebraic
closure. The general resultant premise and the proved polynomial-parameter
substitution can be reused. The rank interpretation, nonzero specialized
polynomial, uniform degree, and exact `D_p` construction remain internal
deductions to establish.

Then prove the exceptional-plane section count and assemble the pointwise
Fourier bound in Lemma 4.4 from the existing ray identity, Katz bound, and
transverse section bound. The analytic assembly leading to Theorems 1.1
and 1.4 remains Pending.
