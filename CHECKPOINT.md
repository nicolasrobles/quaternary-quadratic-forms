# Complete polynomial Fourier estimate checkpoint

## Numbered-result status

Complete: **8**. Partial: **0**. Active numbered targets: **0**.
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
tangent and singular sections. Theorem 1.1, Theorem 1.4, and the next target,
Lemma 4.5, remain Pending.

## Mathematical scope

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

## Current verification

The current milestone registers 325 theorem exports across 66 project
Lean modules and 20 mapped source groups. There are four separately
registered external Lean premises: Weil, the composite Katz/Fulton
spectral interface, Lang's general resultants, and the composite Bertini
and projective-Jacobian tangent interface. Source groups and Lean premise
declarations are counted separately.

The seven new modules have passed strict builds under official Lean 4.24.0 and
the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. The final uniform wrapper compiled successfully
without additional assumptions. All 23 new actual theorem types and axiom
dependencies have been inspected. Seventeen new helpers use only the
standard foundations `propext`, `Classical.choice`, and `Quot.sound`.
The generic and finite-field indicator bounds use Katz and Weil; the
zero-frequency and nonzero-frequency bounds use Katz. The integral
`fourier_bound` uses Katz, Lang, and Weil. The final
`uniform_polynomial_fourier_bound` uses all four unchanged registered
literature premises, including the construction of its exceptional
polynomial.

The full aggregate local verifier passed for all 66 modules, 325 theorem
records, four registered literature-input records, and nine pinned
dependency revisions. All 87 recorded input hashes match the final checked
files. Every one of the 302 previously checked theorem types and axiom
lists is unchanged; their source hashes and scopes are also unchanged.
The four registered premise records and all dependency revisions exactly
match the preceding local report. The frozen manuscript and PDF remain
unchanged.

The [local verification report](certification/verification_report.json)
has SHA-256
`88f51797dd5b426549a351f4cbc62dc24dd51b5d5c57005298b6ee691edcd003`.
The report records 8 Certified and 34 Pending numbered results, with zero
Partial or Active results; all 33 auxiliary/supplementary groups remain
Pending. Whole-paper certification remains false.

GitHub Actions verification of the new proof checkpoint is pending. Its
exact commit, run and downloaded artifact evidence will be recorded after
that execution completes. The preserved runs below cover their stated
preceding scopes.

## Earlier checked checkpoints

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

## Next target

Lemma 4.5 is the next bounded target and remains Pending. For the actual
diagonal forms `F` and `G`, first prove the characteristic-zero smoothness
condition and the equivalence

$$p\nmid N_F\quad\Longrightarrow\quad
\bigl(G\text{ has bad reduction at }p\ \Longleftrightarrow\ p\mid M\bigr).$$

The forward and reverse directions must use the literal gradient-rank
condition and the manuscript's pairwise determinants. In the bad case,
construct the stated two-coordinate point over the algebraic closure.
Then identify the intrinsic bad-prime set and prove the exact formula
`N_G = rad(2αM)` for the already defined modulus.

The characteristic-zero and good-prime matrix hypotheses should be
deduced from the manuscript's diagonal assumptions. The exact formula
must not replace `N_G` by a separately defined surrogate. The analytic
assembly leading to Theorems 1.1 and 1.4 remains Pending.
