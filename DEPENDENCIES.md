# Proof dependencies

These graphs describe the proofs in the frozen
[quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).
Arrows run from a prerequisite to the result that uses it. The
[inventory](INVENTORY.md) gives one row per numbered result and links to checked
Lean exports when they exist. The [live status file](certification/status.json)
governs completion; a dependency in a graph is not a certification claim.

## Three views

| View | Purpose | Files |
|---|---|---|
| Overview | The main proof branches, with related numbered results grouped together | [SVG](docs/dependency_overview.svg), [PDF](docs/dependency_overview.pdf), [PNG](docs/dependency_overview.png) |
| Numbered results | All 42 theorem, lemma, proposition and corollary statements shown separately | [SVG](docs/dependency_graph.svg), [PDF](docs/dependency_graph.pdf), [PNG](docs/dependency_graph.png) |
| Complete graph | The 42 numbered results, 33 auxiliary or supplementary groups, and 20 literature input groups | [Graphviz source](docs/dependency_complete.dot) |

The [machine-readable dependency inventory](certification/dependency_inventory.json)
is the detailed record: 75 internal nodes and 20 source-input nodes, with 137
edges between internal nodes. It retains the reasons for dependencies, exact
source locations, statement text, and the inputs that need formal interfaces.
There are 80 direct dependencies between numbered results.

The numbered-result picture suppresses the auxiliary nodes, preserves paths
through them, and then removes edges already represented by longer paths.
Consequently, the number of visible arrows is smaller than the number in the
detailed record. The overview additionally groups results. An arrow between
groups means that a result in the first group supports a result in the second;
it need not connect every member of the two groups.

## How the proof is organized

**Local arithmetic.** Section 3 works with abstract local functions satisfying
(3.1) and the Fourier hypothesis (3.3). Its Chinese remainder identities,
shared-prime evaluations, modulus sums, singular series, and exceptional-set
averages are proved under those hypotheses. Lemma 2.4 supplies the polynomial
congruence count. The geometric verification in Section 4 is not a premise of
these abstract arguments.

**Geometry and finite-field estimates.** Section 4 constructs exceptional
polynomials of uniformly bounded degree, studies plane sections, and verifies
the Fourier hypothesis for the character weights. Lemma 4.4 combines these
arguments with the bounds of Weil and Katz. Lemmas 4.5 and 4.6 give the separate
explicit diagonal calculation. This branch meets the analytic branch in
Lemma 5.6.

**Analytic assembly.** The central chain is:

1. Lemma 5.1 gives the delta-symbol and Poisson identity.
2. Lemmas 5.2, 5.3 and 5.4 estimate the off-cone, nonzero cone, and zero
   frequencies, respectively, using the local results and integral estimates.
3. Lemma 5.5 assembles the estimates for annular weights.
4. Proposition 5.1 removes the annular-support restriction.
5. Lemma 5.6 specializes the proposition to the actual character sums and
   identifies their local factors.

**The main results and consequences.** Lemma 5.6 gives Theorems 1.1 and 1.4.
Theorem 1.3 combines Theorem 1.1 with the diagonal calculations of Lemmas 4.5
and 4.6. Lemma 5.8 uses Lemma 5.6 in the power sieve and gives Theorem 1.2 and
Corollary 1.1. Corollary 5.7 centers the quadratic characters and cancels the
main term. The relative-asymptotic branch uses the local divisibility and
lower bounds of Lemmas 5.9 and 5.10, together with Lemma 5.6, to prove
Corollary 5.11.

**The determinant method.** Proposition 6.1 is an independent geometric
branch based on Salberger's theorem. Its proof checks the smooth complete
intersection, excludes rational lines, and passes from projective points to
all integral vectors with the required height dependence. It shares a counting
function with the sieve results but does not use their proofs. The comparison
of their bounds at the end of Section 6 is tracked separately.

## Auxiliary claims and coverage

The numbered-result counts are **Complete: 9 · Partial: 0 · Active: 0 · Pending:
33**. Lemmas 2.5 and 2.7, Corollary 2.6, and Lemmas 4.1–4.5 and 5.9 have
complete source-relative proofs. Lemma 4.1 includes finiteness of
the actual bad-prime set, the uniform height bound, and the exceptional-plane
polynomial with its uniform degree and geometric consequences.
Its part (i) also closes the reduction dependency in Lemma 5.9, whose final theorem
uses the literal `p ∤ N_G` hypothesis and proves integrality, divisibility,
and the bound `|a_p(G)| ≤ 4p`.

Lemma 4.4 is complete: all three weight properties (3.1), the exact
zero-frequency clause and pointwise estimate in (4.4), and the full
intermediate ray identity (4.5) are checked. The exceptional section count
includes tangent and singular sections, and the same exceptional polynomial
works for every allowed character. Theorems 1.1 and 1.4 remain Pending. Current and historical
execution evidence is recorded in the checkpoint.

Lemma 4.5 is complete: the actual diagonal pair is smooth in characteristic
zero, its geometric bad primes outside `N_F` are precisely those dividing
the six-factor product `M`, and the existing modulus equals `rad(|2αM|)`.
Its proofs use only standard logical foundations, including the direct
finiteness argument and the treatment of shared prime divisors.

All **33 auxiliary or supplementary groups** remain Pending. These groups
include proof steps needed by the main argument and mathematical assertions
outside numbered theorem environments. They are not added to the
numbered-result count. The 349 theorem exports across 71 Lean modules are
also counted separately from the four external Lean premises. The current
verification scope includes 93 hashed inputs.

Two examples matter throughout the analytic argument: the scaled integral
estimate (5.5), recorded as `aux:Ipiece`, and the weighted singular-series
identity and bound (3.27)-(3.28), recorded as `aux:Sxi` and `aux:Sxibound`.
These remain deductions to establish, not additional assumptions. The detailed
record also retains the counterexamples in Remark 4.1, the modulus-range
consequences, the height thresholds, and the conditional calculation in
Section 7.2. The open questions in the conclusion are not assertions to prove.

## Trusted inputs

We accept the exact literature statements used in the proofs and verify their
hypotheses and the manuscript's deductions. The [source registry](TRUSTED_INPUTS.md)
records these inputs. It distinguishes 20 mapped source groups from the four
registered external Lean premises. The first is the simple-root
univariate Weil estimate from [K, equation (1.2)], specialized to the prime
field; its [declaration](QuaternaryQuadraticForms/Trusted/Weil.lean) and
[source correspondence](certification/correspondence/weil_input.md) fix its
scope.

The second is the [general surface spectral interface](QuaternaryQuadraticForms/Trusted/Katz.lean),
registered against `EXT.KATZ` and `EXT.HYPERSURFACE_CHERN`. This composite
input combines Katz's cohomological concentration, purity, and trace formula
with general hypersurface geometry, the Jacobian interpretation, and the
adjunction and degree formulas documented from Fulton and primary geometric
sources. It supplies spectral data and an unevaluated general Chern
coefficient. The [input review](certification/correspondence/katz_input.md)
discloses the precise boundary.

The quadric's smoothness and geometric irreducibility, the coefficient
`2n²−4n+4`, and the scalar norm inequality are proved internally. The
projective-line, conic, and plane-section deductions retain their earlier
scope. None of these manuscript deductions is registered as an extra premise.

The third premise is the [general homogeneous resultant system](QuaternaryQuadraticForms/Trusted/Elimination.lean),
registered as `EXT.LANG_ELIMINATION`. Lang's theorem supplies one finite
integer family in independent generic coefficients, chosen before the
field and coefficient assignment, whose vanishing detects a nonzero
common zero over the algebraic closure. The
[input review](certification/correspondence/elimination_input.md) records
the exact statement and its treatment of zero specialized forms and empty
output families. Polynomial-parameter substitution, the actual gradient
equations, bad-prime finiteness, and the coefficient-height estimate are
proved internally. The completed Lemma 5.9 uses Lang and Katz, while its
integer divisibility argument uses neither external estimate.

The fourth premise is the [general coordinate Bertini interface](QuaternaryQuadraticForms/Trusted/Bertini.lean),
registered against `EXT.HARTSHORNE_BERTINI` and `EXT.PROJECTIVE_JACOBIAN`.
The [source review](certification/correspondence/bertini_input.md) combines
Hartshorne II.8.18 with explicitly attributed general projective Jacobian,
dimension, component and tangent-space facts. It supplies a hyperplane
normal and a tangent direction for an arbitrary full-rank homogeneous
system over an algebraically closed field. The rank increase, specialization
to the actual quadric and form, resultant construction, descent to the prime
field and uniform degree bound are internal proofs. This interface imposes
no characteristic restriction or divisibility condition on the degrees.

Existing results from official Lean and the pinned official
[mathlib4](https://github.com/leanprover-community/mathlib4) may be reused.

The estimates explicitly refuted by this manuscript are comparison targets,
not trusted premises: [IM, Lemma 4.6], [M, Lemmas 5.3 and 5.4], and the claimed
bound in [M, Proposition 2.1]. Their exclusion is recorded in the same registry.
Trusting a reference does not require assuming an assertion that the paper
itself disproves.

## Completed projective-line and plane-section estimates

Two proved branches meet in Lemma 4.3:

1. [Lemma 2.5](QuaternaryQuadraticForms/WeilBound.lean) applies the registered
   Weil input. [Corollary 2.6](QuaternaryQuadraticForms/ProjectiveWeil.lean)
   deduces the bound for the actual projective-line sum, proving the chart
   decomposition, affine degree, distinct-root condition, and contribution
   at infinity.
2. [Lemma 4.2](QuaternaryQuadraticForms/ConicParametrization.lean) constructs
   one tuple of binary quadratic polynomials over the prime field. Its mapped
   coefficients parametrize the actual conic over every field extension, and
   its formal derivative vectors are independent at every nonzero parameter.
   The construction proves isotropy, the normal form, and compatibility with
   field extension under the manuscript's exact good-prime hypothesis. This
   geometric branch does not depend on the Weil premise.
3. [Lemma 4.3](QuaternaryQuadraticForms/PlaneSectionTheorem.lean) uses the
   conic parametrization to transport the literal section sum to the
   projective line. The rank-three transversality hypothesis proves that the
   degree-`2n` pullback has `2n` distinct geometric projective zeros; no
   restriction that the characteristic be prime to the degree is added.
   Corollary 2.6 then gives the bound `(2n−1)√p+1`.

The correspondence reviews for the
[projective-line bound](certification/correspondence/projective_weil.md),
[uniform conic parametrization](certification/correspondence/conic_parametrization.md),
and [plane-section bound](certification/correspondence/plane_section.md) record
the checked clauses and their actual dependencies.

## Completed quadric Katz estimate

The Katz branch supplies Lemma 2.7:

1. [Quadric geometry](QuaternaryQuadraticForms/QuadricSmooth.lean) computes
   the actual gradient `2 A x` and proves the nonvanishing-gradient condition,
   exact degree, and irreducibility after every field extension.
2. [Projective surface traces](QuaternaryQuadraticForms/ProjectiveSurfaceTrace.lean)
   identify the general hypersurface character sum with the existing matrix
   trace and prove the transverse polynomial nonzero from the rank condition.
3. The registered [Katz/Fulton interface](QuaternaryQuadraticForms/Trusted/Katz.lean)
   gives spectral data for the general smooth geometrically irreducible
   hypersurface with a transverse section. The number of eigenvalues is the
   unevaluated Chern coefficient, and each has norm `p`.
4. [Coefficient arithmetic](QuaternaryQuadraticForms/SurfaceChern.lean)
   verifies the quadric polynomial and computes `2n²−4n+4`. The finite-sum
   triangle inequality gives the scalar bound.
5. [Katz assembly](QuaternaryQuadraticForms/KatzBound.lean) supplies all
   geometric hypotheses from the manuscript's actual matrix and rank-two
   conditions and proves `|a| ≤ (2n²−4n+4)p`.

The [Lemma 2.7 correspondence review](certification/correspondence/katz_quadric.md)
records the actual objects, all local hypotheses, and the distinction between
the general trusted boundary and the internally proved quadric specialization.
There is no restriction that `p` be prime to the degree of `G`.

## Completed ray identity

The first branch now proves (4.5) for the actual sums. Its dependencies are:

1. [Polynomial weights](QuaternaryQuadraticForms/PolynomialWeights.lean):
   homogeneous evaluation, reduction of integral coefficients, vanishing at
   zero, norm at most one, and invariance under nonzero scalar multiplication.
2. [Projective rays](QuaternaryQuadraticForms/ProjectiveRays.lean): a proved
   bijective parametrization of nonzero vectors by actual projective points
   and field units, giving the sum decomposition.
3. [Finite characters](QuaternaryQuadraticForms/FiniteCharacters.lean): the
   standard additive-character sum on each ray is `p − 1` when the phase
   coefficient is zero and `−1` otherwise.
4. [Fourier assembly](QuaternaryQuadraticForms/FourierRays.lean), using the
   [finite algebra](QuaternaryQuadraticForms/RayAlgebra.lean):
   `C_p(u) = p a_u − a`, the zero-frequency formula, and the specialization to
   integral matrices, polynomials, and frequencies. Quadric membership, the
   hyperplane condition, and the character weight are proved independent of
   projective representative.

Positive degree and `ψ ^ n = 1` suffice for this identity; the manuscript's
nonsingularity, smoothness, and nonprincipality hypotheses are not needed at
this stage. The
[correspondence record](certification/correspondence/fourier_rays.md) identifies
the precise clauses checked and the complete assembly below.

## Completed polynomial Fourier bound

The remaining deduction in Lemma 4.4 is now proved for the actual sums.
[PlaneRestriction](QuaternaryQuadraticForms/PlaneRestriction.lean) shows
that a nonsingular symmetric quadratic form cannot vanish identically on
a three-dimensional hyperplane: polarization would put that plane inside
its one-dimensional orthogonal complement. It constructs the actual nonzero
ternary quadratic restriction. The proved mathlib Schwartz–Zippel theorem,
specialized in [PolynomialGridCount](QuaternaryQuadraticForms/PolynomialGridCount.lean),
bounds its affine zeros by `2p²`.

[PlaneSectionCardinality](QuaternaryQuadraticForms/PlaneSectionCardinality.lean)
identifies those zeros with the literal four-coordinate section and proves
that their number is `1 + (p−1)M`, where `M` is its projective cardinality.
For odd primes this implies `M ≤ 2p+2`, including tangent and singular
sections. This is an alternative proof of the manuscript's elementary
incidence-line count; it requires no additional literature premise.

[FourierEstimates](QuaternaryQuadraticForms/FourierEstimates.lean) applies
the actual Katz and plane-section estimates to the exact ray identity.
[FourierBoundConstants](QuaternaryQuadraticForms/FourierBoundConstants.lean)
proves the elementary constant comparisons and the real-power identity
`p^(3/2) = p sqrt(p)`.

| Frequency case | Checked bound |
|---|---|
| `D_p(u) ≠ 0` | `2n² p sqrt(p)` |
| `u ≠ 0`, including the exceptional locus | `2n² p²` |
| `u = 0` | `2n² p²`, from the exact `(p−1)a` identity |

[FourierBound](QuaternaryQuadraticForms/FourierBound.lean) combines these
cases into the actual indicator estimate for every integral frequency.
Its literal `p ∤ N_G` hypothesis supplies odd characteristic,
nonsingularity and geometric good reduction internally. The final export in
[FourierTheorem](QuaternaryQuadraticForms/FourierTheorem.lean) retains the
order `∃ E, ∀ G,p, ∃ D_p, ∀ ψ,u`: the degree bound is uniform in the
coefficients and prime, and the exceptional polynomial is independent of
the character. All three weight conditions and the exact zero-frequency
identity occur explicitly in the same conclusion. No condition `p ∤ n`
is introduced. This uniform export uses precisely the four already
registered Weil, Katz, Lang and composite Bertini premises.

## Completed bad-prime finiteness and height bound

The dependency chain for Lemma 4.1(i) is now proved:

1. [Homogeneous forms](QuaternaryQuadraticForms/HomogeneousForms.lean)
   identify the finite coefficient vector with the actual polynomial.
   [Elimination data](QuaternaryQuadraticForms/EliminationData.lean)
   define the nonzero geometric zero condition.
2. The [registered Lang input](QuaternaryQuadraticForms/Trusted/Elimination.lean)
   supplies a fixed resultant family in independent generic coefficients.
   [Polynomial-parameter substitution](QuaternaryQuadraticForms/EliminationFamily.lean)
   is proved by reconstruction and composition of evaluation.
3. [Rank minors](QuaternaryQuadraticForms/RankMinors.lean) and the
   [literal bad-reduction system](QuaternaryQuadraticForms/BadReductionSystem.lean)
   identify the gradient rank failure with common nonzero zeros. The
   assigned degrees and arbitrary coefficient maps are checked. All ordered
   minors are used, with zero entries and repeated negatives preserving
   the manuscript's common zero locus.
4. The [generic quadric family](QuaternaryQuadraticForms/GenericQuadricFamily.lean)
   fixes `A,n` before introducing the coefficients of `G`.
   [Geometric reduction](QuaternaryQuadraticForms/GeometricReduction.lean)
   identifies the characteristic-zero and prime-field specializations
   with the actual algebraic-closure rank conditions.
5. [Bad-reduction resultants](QuaternaryQuadraticForms/BadReductionResultants.lean)
   yield one fixed family `R_j`. Smoothness gives a nonzero integer value,
   and every bad prime divides it. The
   [arithmetic bridge](QuaternaryQuadraticForms/GoodReduction.lean)
   proves finiteness of the actual bad-prime set and divisibility of its
   distinct-prime product into the absolute value of that integer.
6. [Polynomial evaluation bounds](QuaternaryQuadraticForms/PolynomialHeight.lean)
   give uniform positive constants for the fixed family.
   [The height theorem](QuaternaryQuadraticForms/BadReductionHeight.lean)
   proves `N_G ≤ K H_G^C`, with `∃ C K` before `∀ G` and the literal
   manuscript height and modulus.

The [source correspondence](certification/correspondence/bad_reduction.md)
covers both parts of Lemma 4.1. The selected integer resultant
value may depend on `G`; its fixed family and uniform constants do not.
The proof preserves the intrinsic bad-prime set instead of enlarging it to
all prime divisors of the selected value.

## Completed exceptional-plane polynomial

The second elimination system and the construction in Lemma 4.1(ii) are proved:

1. [Rank-three minors](QuaternaryQuadraticForms/RankThreeMinors.lean)
   identify rank failure with vanishing of all ordered three-column minors.
   [The plane reduction system](QuaternaryQuadraticForms/PlaneReductionSystem.lean)
   consists of the actual `F`, `G`, `u · x`, and those minors. Its 67 equations
   have assigned degrees `2,n,1,n,…,n`. Repeated minors do not change the
   geometric common-zero locus.
2. [Joint-parameter resultants](QuaternaryQuadraticForms/ExceptionalPlaneResultants.lean)
   fix an integral family in the coefficients of `G` and the normal `u`,
   before either is specialized. Its simultaneous zeros detect precisely
   geometric failure of rank-three transversality.
3. [Bertini specialization](QuaternaryQuadraticForms/BertiniPlane.lean)
   applies the general registered input over the algebraic closure and
   proves the rank-three consequence internally using a tangent vector
   annihilated by both gradients but not by the plane normal.
4. [Specialization and descent](QuaternaryQuadraticForms/PlaneResultantSpecialization.lean)
   show that the resulting geometric witness makes one specialized
   resultant polynomial nonzero over the base field. No rational
   transverse plane or injectivity of finite-field polynomial evaluation
   is assumed.
5. [Parameter specialization](QuaternaryQuadraticForms/ParameterSpecialization.lean)
   and the [degree bound](QuaternaryQuadraticForms/ExceptionalPlaneDegree.lean)
   prove that substituting coefficient constants cannot increase total
   degree. The fixed family therefore gives a bound chosen before `G,p`.
6. [The final polynomial theorem](QuaternaryQuadraticForms/ExceptionalPlanePolynomial.lean)
   constructs `D_p = F* R_j(G,·)`, proves that it is nonzero and vanishes
   at the origin, and bounds its degree by `2 + max_j deg R_j`. Its
   nonvanishing implies both `F*(u) ≠ 0` and the literal geometric
   rank-three condition. The final integral wrapper derives all reduction
   hypotheses from the manuscript's `p ∤ N_G`.

The only literature dependencies of the final theorem are Lang and the
general composite Bertini input. The full source correspondence is recorded
in [the Lemma 4.1 review](certification/correspondence/bad_reduction.md).

## Completed quadratic trace theorem

This branch uses the checked zero-frequency identity and the following four
modules:

1. [Matrix polynomial](QuaternaryQuadraticForms/MatrixPolynomial.lean): the
   polynomial representing `xᵀ A x` is homogeneous of degree two, and evaluation
   agrees with the matrix expression.
2. [Quadratic character](QuaternaryQuadraticForms/QuadraticCharacter.lean): the
   integer-valued character, its complex cast, and the usual Legendre symbol
   are identified; its square is the principal character.
3. [Affine divisibility](QuaternaryQuadraticForms/AffineDivisibility.lean):
   Euler's criterion converts the affine character sum modulo `p` into a
   polynomial sum. Mathlib's existing polynomial-grid vanishing theorem applies
   because the total degree is less than `4(p-1)`.
4. [Projective trace](QuaternaryQuadraticForms/QuadraticTrace.lean): the trace is
   constructed as an integer sum and its complex cast is identified with the
   earlier projective trace. The zero-frequency identity becomes an equality
   over the integers. Reducing it modulo `p` transfers divisibility from the
   affine trace to the projective trace.

The resulting statements include integral input coefficients and an explicit
integer witness for the paper's complex-valued trace. Independence of the
integer summand from its projective representative is also proved. The
[correspondence review](certification/correspondence/quadratic_trace.md)
records the exact scope. Odd primality and quadratic homogeneity suffice for
these clauses. The [quadratic trace bounds](QuaternaryQuadraticForms/QuadraticTraceBound.lean)
prove the degree-two size estimate under the actual good-reduction condition
and combine it with the integer witness and divisibility.

[GoodReduction.lean](QuaternaryQuadraticForms/GoodReduction.lean) defines the
exact bad-prime set and finite-product modulus. It proves that avoiding this
modulus is equivalent to avoiding `N_F` and satisfying the geometric rank
condition. Its modulus definition takes an explicit finiteness proof.
The completed elimination argument supplies that proof from the source's
characteristic-zero smoothness assumption.

[QuadraticTraceTheorem.lean](QuaternaryQuadraticForms/QuadraticTraceTheorem.lean)
then proves Lemma 5.9 from the literal manuscript hypotheses. It derives
good reduction from `p ∤ N_G` and combines the actual integer trace,
divisibility, and degree-two Katz bound. The complex export identifies
the projective sum with an integer divisible by `p` and of absolute value
at most `4p`. Neither finiteness nor good reduction is an extra premise
of this final theorem. Its dependencies are the registered Lang and Katz
inputs, with no use of the separate Weil estimate.

## Completed diagonal bad-prime criterion

[DiagonalForms](QuaternaryQuadraticForms/DiagonalForms.lean) identifies the
literal matrix polynomials with the source sums of coefficient-weighted
squares and defines `M` as the product over exactly the six pairs `i < j`.
It proves the coefficient-map identities, nonvanishing of that product,
the nonzero individual first-form coefficients, and `N_F |M| = |2αM|`.

[DiagonalGeometry](QuaternaryQuadraticForms/DiagonalGeometry.lean) calculates
the actual gradient minors as `4 x_i x_j (a_i b_j - a_j b_i)`. When all
pair differences are nonzero and two is nonzero, simultaneous vanishing
of these minors leaves at most one nonzero coordinate. The actual first
quadratic equation then excludes every nonzero vector. Conversely, a
vanishing pair difference gives the explicit geometric point
`x = e_i + z e_j`, where `z² = -a_i/a_j`. Both equations and actual rank
failure are proved for that point over the algebraically closed field.

[DiagonalReduction](QuaternaryQuadraticForms/DiagonalReduction.lean) applies
this geometry to the literal characteristic-zero smoothness predicate and
to `GoodReductionAt`. At a prime outside `N_F`, nonsingularity and odd
characteristic follow internally. The six-factor product maps through
reduction and the injective algebraic-closure map, giving exactly
`¬ GoodReductionAt p A G ↔ (p : ℤ) ∣ M`.

[BadPrimeRadical](QuaternaryQuadraticForms/BadPrimeRadical.lean) proves the
arithmetic consequence of this actual geometric criterion. The nonzero
integer `M` gives finiteness directly. The additional bad-prime finset is
`primeFactors(|M|) \ primeFactors(N_F)`; its product together with
`rad(N_F)` is the radical of `N_F |M|`, with common prime factors included
once. [DiagonalBadPrimes](QuaternaryQuadraticForms/DiagonalBadPrimes.lean)
combines all three clauses of Lemma 4.5 and proves the existing modulus
equality for every proof of finiteness supplied to its definition.

All 24 new exports have only the standard logical foundations in their
inspected axiom lists. No elimination or other registered literature
premise is used. Zero coefficients `b_i`, negative coefficients and `M`,
overlapping prime divisors, and `p = 3` outside `N_F` are covered. The
[source review](certification/correspondence/diagonal_bad_primes.md) records
the actual hypotheses and every clause.

## Next proof branch

Lemma 4.6 remains Pending and is the next target. First establish the
shared one-dimensional prime-field Gauss identities using proved library
results and the existing actual complex quadratic character and standard
additive character. Define the literal `t_i`, `κ_i`, `Φ_u` and `ν_i`, and
prove the exact Fourier pencil formula with all four singular members.
Then deduce the zero-frequency projective trace and the generic
`2p^(3/2)+4p` bound, including the repeated-root cubic cases. The four
distinct `t_i` supply `p ≥ 5` in this later lemma.

The full prime-power statement of Lemma 3.2 remains Pending; proving a
shared scalar helper does not certify its other clauses. The main analytic
theorems remain Pending.

The graphs can be regenerated from the detailed inventory with
`python3 scripts/build_dependency_graph.py`. Graph rendering needs Graphviz;
checking the Lean proofs does not.
