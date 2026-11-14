# Proof dependencies

These graphs describe the proofs in the frozen
[v35 manuscript](manuscript/quadratic_character_sums_github.tex).
Arrows run from a prerequisite to the result that uses it. The
[inventory](INVENTORY.md) gives one row per numbered result and links to checked
Lean exports when they exist. The [live status file](certification/status.json)
governs completion; a dependency in a graph is not a certification claim.

## Three views

| View | Purpose | Files |
|---|---|---|
| Overview | The main proof branches, with related numbered results grouped together | [SVG](docs/dependency_overview.svg), [PDF](docs/dependency_overview.pdf), [PNG](docs/dependency_overview.png) |
| Numbered results | All 42 theorem, lemma, proposition and corollary statements shown separately | [SVG](docs/dependency_graph.svg), [PDF](docs/dependency_graph.pdf), [PNG](docs/dependency_graph.png) |
| Complete graph | The 42 numbered results, 33 auxiliary or supplementary groups, and 19 literature input groups | [Graphviz source](docs/dependency_complete.dot) |

The [machine-readable dependency inventory](certification/dependency_inventory.json)
is the detailed record: 75 internal nodes and 19 source-input nodes, with 137
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

The numbered-result counts are **Complete: 5 · Partial: 2 · Active: 0 · Pending:
35**. Lemmas 2.5 and 2.7, Corollary 2.6, and Lemmas 4.2 and 4.3 have complete
source-relative proofs. The new Katz milestone passed the full local
verifier; current execution evidence is recorded in the checkpoint.
The projective-line and conic arguments give the transverse section bound,
and the new branch gives the complete quadric trace bound.

Lemma 4.4 is Partial: all three weight properties (3.1), the exact
zero-frequency clause of (4.4), and the full intermediate ray identity (4.5)
are checked. Its pointwise Fourier estimate remains pending. Lemma 5.9 is
Partial: integrality and divisibility of the actual projective trace are
checked, and the bound `|a_p(G)| ≤ 4p` is proved under literal good reduction.
The `N_G` wrappers still require a proof that the bad-prime set is finite;
obtaining that proof from characteristic-zero smoothness remains pending.

All **33 auxiliary or supplementary groups** remain Pending. These groups
include proof steps needed by the main argument and mathematical assertions
outside numbered theorem environments. They are not added to the
numbered-result count. The 207 theorem exports across 38 Lean modules are
also counted separately from the two external Lean premises. The current
verification scope includes 56 hashed inputs.

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
records these inputs. Its 19 mapped groups are not 19 Lean axioms. Two
external Lean premises are registered. The first is the simple-root
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

The new branch supplies Lemma 2.7:

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
the precise clauses checked. The plane-section estimate of Lemma 4.3 is now
available, as is the global Katz bound in Lemma 2.7. The `D_p`-dependent
bound in Lemma 4.4 still needs the exceptional-polynomial construction in
Lemma 4.1, the exceptional plane-section count, and the final Fourier
assembly. Those remaining steps have not been assumed as additional premises.

## The quadratic trace and the remaining reduction dependency

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
these clauses. The new [quadratic trace bounds](QuaternaryQuadraticForms/QuadraticTraceBound.lean)
prove the degree-two size estimate under the actual good-reduction condition
and combine it with the integer witness and divisibility.

[GoodReduction.lean](QuaternaryQuadraticForms/GoodReduction.lean) defines the
exact bad-prime set and finite-product modulus. It proves that avoiding this
modulus is equivalent to avoiding `N_F` and satisfying the geometric rank
condition. The finiteness proof is explicit in this definition and in the
final trace wrappers. It also proves finiteness and the product bound from
any nonzero integer divisible by every bad prime. The still-unproved
elimination witness in Lemma 4.1(i) must provide that integer from the source's
characteristic-zero smoothness assumption. This is why Lemma 5.9 remains Partial.

## Next proof branch

The next target is the elimination witness in Lemma 4.1(i), giving a nonzero
integer `P_i(G)` divisible by every bad prime from the characteristic-zero
rank condition. The proved arithmetic bridge then yields finiteness of the
actual bad-prime set and completes the missing reduction step in Lemma 5.9.

The height bound for `N_G`, the exceptional-polynomial construction in
Lemma 4.1(ii), and the exceptional-section count and Fourier assembly remain
further obligations. The global Katz estimate, plane-section estimate, exact
ray identity, and quadratic-trace integrality and divisibility are available
as proved inputs.

The graphs can be regenerated from the detailed inventory with
`python3 scripts/build_dependency_graph.py`. Graph rendering needs Graphviz;
checking the Lean proofs does not.
