# Conic parametrization and plane-section checkpoint

## Numbered-result status

Complete: **4**. Partial: **2**. Active numbered targets: **0**.
Pending: **36**. All 33 auxiliary/supplementary groups remain Pending.

**Lemma 2.5 and Corollary 2.6 are Certified relative to the accepted literature
inputs.** The first is matched to the cited simple-root univariate Weil bound.
The second is proved under the literal manuscript hypotheses, with the
projective charts, affine polynomial, degree, and geometric-root deductions
checked in Lean.

**Lemmas 4.2 and 4.3 are now Certified.** The conic parametrization uses one tuple of actual binary quadratic
forms over every field extension. The plane-section estimate uses the literal
geometric rank-three hypothesis and the actual projective character sum.
The full local verifier and source correspondence review have passed.
GitHub Actions verification for this milestone is pending publication.

Lemma 4.4 retains its checked weight properties, ray identity (4.5), and exact
zero-frequency clause; its pointwise estimate remains pending. Lemma 5.9
retains its checked integrality and divisibility clauses; its size bound
|a_p(G)| ≤ 4p remains pending. Both results remain Partial.

## Mathematical scope

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

### Local execution

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

All 47 recorded input hashes match the checked files, including the six
correspondence records. The final actual type of `conic_parametrization`
chooses the tuple before quantifying over extension fields. The final type of
`plane_section_bound` assumes the literal geometric matrix-rank condition
and constructs the parametrizations internally. Independent source review
found no missing clause or strengthened manuscript hypothesis.

- [Local verification report, actual types, and input hashes](certification/verification_report.json).
- Lean: official 4.24.0.
- mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- Manuscript SHA-256: `d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.

### GitHub execution

Publication and GitHub Actions verification for this checkpoint are pending.
The successful runs below are retained as evidence for their earlier scopes.

## Earlier checked checkpoints

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

The next target is the exact Katz literature interface and its geometric
specialization in Lemma 2.7. Its global trace estimate is needed for the
remaining size clause `|a_p(G)| ≤ 4p` in Lemma 5.9; the checked integrality
and divisibility clauses remain available.

The exceptional-polynomial construction in Lemma 4.1 and the pointwise Fourier
bound in Lemma 4.4 remain separate pending obligations. The new plane-section
bound supplies one required input, but does not complete the exceptional-plane
construction, the exceptional-section counting step, or the Fourier estimate.
