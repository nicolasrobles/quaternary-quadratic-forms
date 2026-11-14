# Character sums over zeros of quaternary quadratic forms

Source-relative Lean verification of the paper by Hemjyoti Nath, Nicolas Robles,
and Alexandru Zaharescu.

The mathematical source is the audited frozen manuscript
[quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).
The associated [34-page PDF](manuscript/quadratic_character_sums_github.pdf) is
included. The source SHA-256 is

    d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33

## Current status

**Complete: 7 · Partial: 1 · Active: 0 · Pending: 34** — 42 numbered results.

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

Lemma 4.4 remains **Partial**: its three weight properties, exact
zero-frequency formula, and ray identity (4.5) are checked. The newly
available `D_p` supplies its exceptional set; the exceptional-section
point count and final pointwise Fourier estimate remain to be proved.
Theorems 1.1 and 1.4 remain Pending.

This milestone covers 302 theorem exports across 59 Lean modules, four
separately registered external Lean premises, and 20 mapped source groups.
All 33 auxiliary/supplementary groups remain Pending. This repository does
not yet provide a certificate for the whole paper.

**The full local verifier passed for the current checkpoint:** all 59 modules,
302 theorem exports, four exact registered literature premises and 80 input
hashes were checked under the pinned Lean settings. All 261 previously
checked theorem types and axiom dependencies are unchanged. The independent
GitHub Actions run for this scope is pending. The execution checkpoint
records the scope and evidence for each run.

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
- [Correspondence review for the Fourier ray identity](certification/correspondence/fourier_rays.md)
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
The manuscript's hypotheses therefore specialize the checked results. The
remaining clause of Lemma 4.4 is the bound involving the exceptional polynomial
`D_p`, whose construction and properties are now checked in Lemma 4.1(ii).
The remaining proof combines the generic transverse-section estimate with
the exceptional-section point count and the numerical constants. The
[correspondence record](certification/correspondence/fourier_rays.md) separates
the completed clauses from those obligations.

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
      Mathlib.RingTheory.MvPolynomial.EulerIdentity \
      Mathlib.Tactic.FieldSimp \
      Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex \
      Mathlib.Data.Nat.Factorization.Basic \
      Mathlib.Algebra.Polynomial.Coeff \
      Mathlib.Algebra.MvPolynomial.Eval \
      Mathlib.Algebra.MvPolynomial.Degrees \
      Mathlib.Algebra.MvPolynomial.Variables \
      Mathlib.Algebra.Order.BigOperators.Group.Finset \
      Mathlib.Data.Finsupp.Weight \
      Mathlib.Tactic.IntervalCases \
      Mathlib.Tactic.FinCases \
      Mathlib.Tactic.LinearCombination \
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

The next target is the remaining pointwise Fourier estimate in Lemma 4.4.
The exceptional polynomial `D_p` and all its required properties are now
available from complete Lemma 4.1. The existing Katz estimate, transverse
plane-section estimate, and exact ray identity handle the zero and generic
frequencies. The exceptional-section point count and the final constant
comparisons must be proved and assembled under the exact manuscript
hypotheses. The analytic assembly and main theorems remain Pending.
