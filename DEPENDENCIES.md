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
| Complete graph | The 42 numbered results, 33 auxiliary or supplementary groups, and 21 literature input groups | [Graphviz source](docs/dependency_complete.dot) |

The [machine-readable dependency inventory](certification/dependency_inventory.json)
is the detailed record: 75 internal nodes and 21 source-input nodes, with 137
edges between internal nodes. It retains the reasons for dependencies, exact
source locations, statement text, and the inputs that need formal interfaces.
There are 80 direct dependencies between numbered results.

The numbered-result picture suppresses the auxiliary nodes, preserves paths
through them, and then removes edges already represented by longer paths.
Consequently, the number of visible arrows is smaller than the number in the
detailed record. The overview additionally groups results. An arrow between
groups means that a result in the first group supports a result in the second;
it need not connect every member of the two groups.

## Current Lemma 2.3 checkpoint

**Lemma 2.3 is Certified in full.** The actual finite set of integer zeros
of a symmetric nonsingular rational quaternary form with nonsquare rational
determinant satisfies the Euclidean `U^(2+epsilon)` bound. For every positive
epsilon, one positive constant is selected before all real `U>=1`.
The rational hyperbolic splitting, binary anisotropy from the determinant,
positive denominator clearing, injective lattice map, signed-divisor count,
and zero binary-coordinate slice are proved internally. All 28 new exports
use only the standard logical foundations and add no literature premise.
See the [source endpoint](QuaternaryQuadraticForms/QuadricCountingTheorem.lean),
[source review](certification/correspondence/quadric_count.md), and
[execution checkpoint](CHECKPOINT.md). The weighted consequence
`aux:conecount` remains Pending; this session stops after Lemma 2.3.

## Earlier analytic and coefficient checkpoint

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

The shared weight family has common coordinate derivative bounds and support
in a fixed annulus. The final theorem chooses the localization scale first,
then uses the finite family of actual signed coordinate isometries to select
common constants before every piece, scale, and frequency. The actual
quadratic gradient and Hessian, uniform annular gradient lower bound,
coordinate pullback, positive-root chart, and surface-integral transport are
proved in Lean. The bounded-scale source estimates extend internally to all
`r>0` using the common kernel cutoff, including the zero-frequency error.
This completes Lemma 2.2 and aux:weight_pieces; the separate general
cone-vertex integrability and scaled-integral obligations retain their own
Pending status.

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

The numbered-result counts are **Complete: 25 · Partial: 0 · Active: 0 · Pending:
17**. Lemmas 2.1–2.7, Lemmas 3.1–3.11, and Lemmas 4.1–4.6 and 5.9
have complete source-relative proofs (including Corollary 2.6). Lemma 4.1 includes finiteness of
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

Lemma 4.6 is complete for the literal integral input data: the exact pencil
formula retains all four singular members, zero frequency gives the actual
integer projective trace, and the generic Fourier bound is
`2p^(3/2)+4p`. The exact formula and trace use no external premise. The
bound uses only the existing Weil premise, with repeated-root cubics
handled internally. Theorem 1.3 remains Pending because its asymptotic
clause still depends on Theorem 1.1.

Lemma 3.1 is complete for the literal prime-product weights and mixed
complete sums: both CRT multiplicativity and invariance under every
integer frequency scalar coprime to `qc` are checked. The final source
wrapper accepts local functions only at primes not dividing `N`, with
no assumptions on excluded primes. Lift independence, modulus one,
the direct `C_q` prime-factor product and `S_c` multiplicativity, and the
bridge to the existing prime Fourier sum are proved. Its 66 exports
have passed strict builds and actual type and axiom inspection; all use
only standard logical foundations. Aggregate verification and CI
execution evidence are recorded separately in the checkpoint.

Lemma 3.2 is complete for the source's general symmetric integral matrix:
the full shifted Gauss evaluation at every good prime power, the exact
Ramanujan formula for `S_{p^k}`, and the cardinality of the actual
projective quadric. The good-prime condition uses precisely
`N_F=2|det A|`, and the coefficient is the stated Legendre symbol
`χ(p)=(det A/p)`. The prime base case, digit recurrence, square completion,
unit permutations and affine/projective count are proved internally.
The 54 supporting exports in 16 new modules introduce no literature
premise. Actual type and dependency inspection, aggregate verification
and CI execution evidence are recorded separately in the checkpoint.

Lemma 3.3 is complete for every positive modulus and every integral
frequency. Its exact bound is `|S_c(u)|≤4√|det A| c³` for the existing
complete sum, assuming only symmetry and integer nonsingularity of
the actual matrix. The squared-norm identity selects the actual
residue kernel of `2A`; its cardinality is bounded using integer
range indices, surjective coefficient reduction, and the proved
Smith-normal-form determinant-index theorem in mathlib. All 17 new
exports in eight modules use only standard logical foundations.
Modulus one, even moduli, and arbitrary bad-prime factors are included.
Aggregate verification and CI evidence are recorded separately in
the checkpoint.

Lemma 3.4 is complete for every `k≥1` and integral frequency, with the
original supplied local weight at a source prime `p∤N`. The actual
weighted sum `𝒰_j`, its stationary residue expansion, and invariance
under nonzero scalars give the adjugate-frequency weight. The actual
unit-digit bijection proves `𝒰_{k+1}=p 𝒮_{p,p^k}` with the literal
constraint `p∣F(x)`. Cancelling the nonzero scalar `p` gives the exact
power `p^(2k+1)`. The source radical condition `rad(N_F)∣N` supplies
good reduction from `det A≠0`. All 18 new exports in eight modules
use only standard logical foundations; no literature premise is added.
Aggregate verification and CI execution evidence are recorded separately
in the checkpoint.

Lemma 3.5 is complete in both clauses, with the actual factors
`q₁=gcd(q,c)` and `q₂=q/q₁`. Prime-power CRT induction proves the
global formula at moduli coprime to `N_F`. The dual-cone identity
holds at every positive modulus, including arbitrary bad-prime
factors; the bad-part sum is multiplied through without cancellation.
The source endpoints retain an actual supplied Dirichlet character
and the product of the original supplied prime weights. Agreement
between the Jacobi coefficient and the character at good composite
moduli is proved from its stated good-prime values. The 27 new
exports in 11 modules use only standard logical foundations and
introduce no literature premise. Aggregate verification and CI
execution evidence are recorded separately in the checkpoint.

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

The **33 auxiliary or supplementary groups** comprise **5 Certified and
28 Pending** claims. The polynomial-box epsilon consequence, aux:Cfactor,
aux:weight_pieces, aux:Sxi, and aux:Sxibound are complete. These groups include
proof steps needed by the main argument and mathematical assertions outside numbered theorem
environments; they are not added to the numbered-result count. The current
scope contains **1,115 theorem exports across 256 Lean modules**, counted
separately from the **11 external Lean premises**. It includes **296 inspected
inputs**, nine pinned dependency revisions, and **21 mapped source groups**.
Strict declaration inspection, source review, and current local aggregate
and exact-commit CI execution evidence for the combined scope are recorded
separately in the checkpoint. Historical aggregate evidence retains
its original scope. The whole-paper
certification flag remains false.

The scaled integral estimate (5.5), recorded as `aux:Ipiece`, remains a
deduction to establish. The weighted singular-series identity and bound
(3.27)–(3.28), recorded as `aux:Sxi` and `aux:Sxibound`, are now proved
internally from the completed Fourier-product and singular-series results. The detailed
record also retains the counterexamples in Remark 4.1, the modulus-range
consequences, the height thresholds, and the conditional calculation in
Section 7.2. The open questions in the conclusion are not assertions to prove.

## Trusted inputs

We accept the exact literature statements used in the proofs and verify their
hypotheses and the manuscript's deductions. The [source registry](TRUSTED_INPUTS.md)
records these inputs. It distinguishes 21 mapped source groups from the
11 registered external Lean premises. The first is the simple-root
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

The fifth premise is the [fixed Heath–Brown delta construction](QuaternaryQuadraticForms/Trusted/HeathBrown.lean).
Its [source review](certification/correspondence/delta_symbol.md) records the
actual bump, sampling sum, kernel properties, unnormalized delta identity,
and raw sampling estimate. The uniform positive normalization for real
`Q>=3`, exact normalized identity, original residue phases, and finite outer
support of Lemma 2.1 are internal deductions.

Lemma 2.2 adds five [Heath–Brown analytic inputs](QuaternaryQuadraticForms/Trusted/HeathBrownIntegrals.lean):
uniform localization, the thin-slab graph limit, zero-frequency approximation,
fixed-frequency integral reduction, and auxiliary oscillatory estimates.
Their [source review](certification/correspondence/delta_integrals.md) records
all weight, derivative, amplitude, and geometric bounds before the individual
weight, scale, and frequency, and keeps the cited estimates on a fixed bounded
positive scale range. The real-coefficient scope is justified by the inspected
analytic arguments. Their extension to all positive scales uses the actual
kernel cutoff internally.

The remaining new premise is [Simon's general graph area formula](QuaternaryQuadraticForms/Trusted/SimonArea.lean),
registered as `EXT.SIMON_GRAPH_AREA`. Its
[source review](certification/correspondence/surface_area_formula.md) fixes the
normalization of Euclidean surface measure relative to mathlib's raw
Hausdorff measure. Heath–Brown's graph-coordinate expression is connected to
the manuscript's actual surface integral by a proved quadratic chart,
Jacobian-to-gradient identity, support restriction, and complex integration
argument. No manuscript-specific normalization or internal geometry is
accepted as an extra premise. The newly Certified weight-piece construction
uses only standard logical foundations.

Existing results from official Lean and the pinned official
[mathlib4](https://github.com/leanprover-community/mathlib4) may be reused.
The prime-field quadratic Gauss identities needed for Lemma 4.6 are proved
from those library results in
[PrimeQuadraticGauss](QuaternaryQuadraticForms/PrimeQuadraticGauss.lean).
The source's Gauss-sum citation does not introduce an additional Lean premise.
The exact pencil formula and trace use no literature premise, and the
generic bound uses the already registered affine Weil estimate only in
the separable cubic case.

The complete-sum definitions, source-domain weight extension, scaled CRT,
phase calculations, unit-frequency invariance and factorization corollaries
for Lemma 3.1 likewise use only proved library results and standard logical
foundations. No literature premise is added for this arithmetic branch.

The full prime-power evaluation and point count in Lemma 3.2 likewise
use only proved library results and standard logical foundations. The
orthogonal-basis theorem and the existing prime-field Gauss identities
provide the general matrix base case. All residue-digit calculations,
the recurrence, adjugate square completion, Ramanujan reindexing and
actual point counts are internal deductions. No source-specific Gauss
evaluation, diagonalization conclusion, recurrence or count is accepted
as a premise in the final statements.

The bound at arbitrary moduli in Lemma 3.3 also uses no registered
literature premise. The conjugate-product identity, composite-modulus
orthogonality, actual residue kernel, coefficient-reduction maps, and
complete-sum triangle inequality are internal deductions. Mathlib's
`Submodule.natAbs_det_equiv` is a proved general determinant-index
theorem, whose proof uses Smith normal form. Its application here
proves the required actual kernel bound; no source-specific kernel
count or inner Gauss estimate is assumed.

The shared-prime identity in Lemma 3.4 uses no registered literature
premise. Its literal weighted Gauss sums, stationary residue expansion,
adjugate calculation, nonzero scalar, and actual unit-digit bijection
are proved internally. The completed Lemma 3.2 evaluates the remaining
unweighted sum. The source-domain extension is identified with the
original supplied function, and the exact radical divisibility
hypothesis supplies good reduction. Neither a weighted extraction nor
the identity `𝒰_{k+1}=p 𝒮_{p,p^k}` is assumed in the final theorem.

The two global identities in Lemma 3.5 likewise use no registered
literature premise. Actual Ramanujan CRT, the unit count at zero,
the divisor-totient identity, gcd/quotient arithmetic, and the
constructed bad/good prime-support split are internal deductions.
The source's supplied Dirichlet character is an actual
`DirichletCharacter`; prime induction proves its composite agreement
with the Jacobi coefficient from exactly the given Legendre values.
No equality at composite moduli, CRT factorization, or nonvanishing
of the bad-part sum is assumed in either final source clause.

The absolute modulus bound in Lemma 3.6 also uses no registered literature
premise. Its Ramanujan recurrences, gcd estimate, divisibility support,
finite factor-pair transport, prime-support count, and uniform divisor and
logarithm estimates are internal proofs over the pinned library. It does
not assume the source local series or a bound for the complete modulus
sum. The broader Ramanujan auxiliary group remains separately Pending.

The dual-cone cancellation bound in Lemma 3.7 also uses no registered literature
premise. The actual good Jacobi coefficient, derived nonprincipality, zero
period sum, cubic cancellation, exact Möbius/totient rearrangement, and
bad/good finite-sum factorization are internal proofs over the pinned library.
The positive constant is uniform over q,d,e,u,X and depends only on the
fixed form and the positive exponent. No primitive-conductor formula or
internal cancellation estimate is added to the trusted-input registry.

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

## Completed diagonal pencil formula and bound

All three clauses of Lemma 4.6 are proved for the actual integral diagonal
forms and frequencies, under the literal restriction `p ∤ 2αM`:

1. [PrimeQuadraticGauss](QuaternaryQuadraticForms/PrimeQuadraticGauss.lean)
   defines the actual complex quadratic Gauss sum and proves its
   nonvanishing, square and fourth-power identities, Gauss inversion,
   and the one-dimensional quadratic exponential sum. Completing the
   square uses the standard additive character, and zero quadratic
   coefficients have their separate exact evaluation.
   [PrimeRamanujan](QuaternaryQuadraticForms/PrimeRamanujan.lean) defines
   the actual sum over units and proves both values, including `R_p(0)=p−1`,
   together with the reciprocal-phase identity.
2. [DiagonalPencil](QuaternaryQuadraticForms/DiagonalPencil.lean) defines
   the literal `t_i`, `κ_i`, `Φ_u`, `ν_i`, coefficient products, and
   reciprocal phases. [DiagonalPencilAlgebra](QuaternaryQuadraticForms/DiagonalPencilAlgebra.lean)
   checks the field identities, all nonzero denominators, and distinctness
   of the four singular parameters, which implies `p ≥ 5`.
   [DiagonalPencilCubic](QuaternaryQuadraticForms/DiagonalPencilCubic.lean)
   proves the formal degree bound and identifies the coefficient of `t³`
   with the actual adjugate dual value `F*(u)`.
3. [FourierOrthogonality](QuaternaryQuadraticForms/FourierOrthogonality.lean)
   expands the actual quadric constraint and factors the four coordinate
   sums. [FourierGaussExpansion](QuaternaryQuadraticForms/FourierGaussExpansion.lean)
   removes the zero Gauss parameter before the substitution `v = s t`
   and proves the exact identity `(p τ_p) C_p(u) = ∑_t rawSum(t)`.
4. [DiagonalPencilEvaluation](QuaternaryQuadraticForms/DiagonalPencilEvaluation.lean)
   evaluates each regular raw term as `p² τ_p χ_p(-Φ_u(t))`.
   Each singular raw term is `p² τ_p χ_p(κ_i) R_p(ν_i(u))` when
   `u_i=0`, and zero otherwise. The signs and powers follow from
   `-Δ_i=κ_i/a_i⁴` and the exact nonzero factor relating `w_i` to
   `ν_i(u)`. [DiagonalPencilFormula](QuaternaryQuadraticForms/DiagonalPencilFormula.lean)
   splits the parameter sum into its complement and all four distinct
   singular parameters, then cancels the proved nonzero factor `p τ_p`.
5. [CubicCharacterSum](QuaternaryQuadraticForms/CubicCharacterSum.lean)
   handles every cubic. The separable case uses the existing affine
   Weil estimate. Over the perfect prime field, a nonseparable cubic
   factors as `c (X-a)² (X-b)` with both roots in that field; its exact
   character sum is `-χ_p(c(a-b))`, also covering the triple-root case.
   Deleting the four singular parameters therefore costs at most four.
6. [DiagonalPencilConsequences](QuaternaryQuadraticForms/DiagonalPencilConsequences.lean)
   specializes zero frequency and the checked projective-ray identity
   to obtain `a_p(G)=p ∑_i χ_p(κ_i)`. When every `u_i` and `F*(u)` are
   nonzero, the singular sum vanishes, `Φ_u` has degree three, and the
   cubic estimate gives `2p^(3/2)+4p`.
7. [DiagonalPencilReduction](QuaternaryQuadraticForms/DiagonalPencilReduction.lean)
   derives every field hypothesis from the source divisibility conditions
   and verifies the coefficient maps of the dual form.
   [DiagonalPencilTheorem](QuaternaryQuadraticForms/DiagonalPencilTheorem.lean)
   gives the exact integral Fourier formula, the integer projective trace,
   the generic bound, and one combined export for every clause.

The [source correspondence review](certification/correspondence/diagonal_pencil.md)
records the literal objects and normalization throughout this chain.
The Gauss calculations, rational identities, singular terms, exact trace,
and repeated-root argument use only standard logical foundations and
proved library results. The final bound and combined theorem add only
the existing Weil premise. No separability assumption is imposed on
`Φ_u`, and neither `ν_i(u)=0` nor a vanishing coefficient `b_i` is excluded.

## Completed CRT factorization and frequency invariance

Both clauses of Lemma 3.1 are proved for the source's actual integral
quadratic form, frequency, prime-product weights and mixed complete sums:

1. [CompositeWeights](QuaternaryQuadraticForms/CompositeWeights.lean)
   defines `ξ_q(x)` as the product over `q.primeFactors`, proves `ξ_1=1`
   and prime specialization, and checks congruence, periodicity, coprime
   products and scalar invariance. Its residue-ring version agrees with
   every integer lift when `q` divides the ambient modulus.
   [SourceWeights](QuaternaryQuadraticForms/SourceWeights.lean) accepts
   functions only at primes `p ∤ N` and extends the family by zero outside
   that domain. When `(q,N)=1`, every factor equals the supplied local
   function; no property at an excluded prime enters the argument.
2. [CompleteSumAlgebra](QuaternaryQuadraticForms/CompleteSumAlgebra.lean)
   proves the quadratic-value reduction and homogeneity identities for
   the actual matrix polynomial.
   [CompleteSums](QuaternaryQuadraticForms/CompleteSums.lean) defines
   `C_q`, `S_c` and `𝒮_{q,c}` using the standard additive character and
   proves independence of the representatives of both `x mod qc` and
   `a mod c`. The latter uses precisely the constraint `q ∣ F(x)`.
3. [CRTCharacters](QuaternaryQuadraticForms/CRTCharacters.lean) proves
   the exact additive-character identities, including modulus one.
   [CRTArithmetic](QuaternaryQuadraticForms/CRTArithmetic.lean) constructs
   the scaled CRT bijections for residues, units and four-dimensional
   vectors. With `n_i=q_i c_i`, the vector is `x=n_2 x_1+n_1 x_2`,
   and the unit parameter is `a=c_2 a_1+c_1 a_2`.
4. [MixedPhase](QuaternaryQuadraticForms/MixedPhase.lean) checks the
   source phase factors `c_2 n_2` and `c_1 n_1` using the two local cone
   conditions. [CompleteSumCRT](QuaternaryQuadraticForms/CompleteSumCRT.lean)
   proves the equivalence of the global and local cone conditions,
   splits the actual weight and phase, reindexes the finite sums, and
   absorbs those factors by unit permutations. Its only coprimality
   condition is `(q_1 c_1,q_2 c_2)=1`; shared prime divisors of `q_i`
   and `c_i` within a block are allowed. The product-defined extension
   satisfies this theorem even without the source's squarefreeness
   restriction.
5. [CompleteSumInvariance](QuaternaryQuadraticForms/CompleteSumInvariance.lean)
   proves `𝒮_{q,c}(tu)=𝒮_{q,c}(u)` under the literal integer condition
   `(t,qc)=1`, through inverse scaling of `x` and square scaling of the
   unit parameter. Modulus one is included throughout. The allowed case
   `t=0` is retained: its gcd hypothesis forces `qc=1`.
6. [CompleteSumSpecializations](QuaternaryQuadraticForms/CompleteSumSpecializations.lean)
   proves `𝒮_{1,c}=S_c`, `𝒮_{q,1}=C_q`, their modulus-one values, and
   the equality of the prime polynomial-character specialization with
   the existing `integralFourierSum`.
   [CompleteSumFactorization](QuaternaryQuadraticForms/CompleteSumFactorization.lean)
   deduces multiplicativity of `S_c` and the actual squarefree product
   `C_q(u)=∏_{p∣q} C_p(u)`, including the empty product at `q=1`.
   [CompleteSumTheorem](QuaternaryQuadraticForms/CompleteSumTheorem.lean)
   supplies the combined theorem and its final source-domain wrapper.

The [source correspondence review](certification/correspondence/complete_sum_crt.md)
records both numbered clauses, the supplied-prime domain, the exact
normalizations and the direct supporting corollaries. All 66 exports in
these 12 modules use only standard logical foundations and proved library
results. The separate auxiliary-group ledger is unchanged; the new
supporting exports do not automatically certify an entire auxiliary group.

## Completed prime-power Gauss evaluation and point count

All three clauses of Lemma 3.2 are proved for the actual source objects.
For a prime `p ∤ N_F`, where `N_F=2|det A|`, write `α=det A` and
`χ(p)=(α/p)`. The integral frequency is arbitrary. For `k≥1` the
checked statements are

- `∑_x e_{p^k}(aF(x)+u·x) = χ(p)^k p^(2k) e_{p^k}(-(4aα)⁻¹F*(u))`
  whenever `p ∤ a`;
- `S_{p^k}(u)=χ(p)^k p^(2k) R_{p^k}(F*(u))` for the literal
  unweighted complete sum and Ramanujan unit sum;
- `#Q(F_p)=p²+(1+χ(p))p+1` for the actual projective zero set of
  the reduced matrix quadratic form.

The complete proof chain is:

1. [QuadraticGaussSums](QuaternaryQuadraticForms/QuadraticGaussSums.lean)
   defines the literal finite Gauss sum and its integral specialization.
   [IntegralGaussSums](QuaternaryQuadraticForms/IntegralGaussSums.lean)
   identifies it with the canonical-lift expression, proves the zero
   coefficient and modulus-one values, and identifies `S_c` with its
   actual outer sum over the unit group.
2. [PrimePowerUnits](QuaternaryQuadraticForms/PrimePowerUnits.lean)
   derives the unit hypotheses at `p^k` from `p ∤ N_F` and `p ∤ a`.
   The source good-prime condition supplies oddness and invertibility
   of the actual reduced determinant; these are not extra assumptions.
3. [MatrixSquareCompletion](QuaternaryQuadraticForms/MatrixSquareCompletion.lean)
   proves the adjugate translation identity over any commutative ring.
   [QuadraticGaussShift](QuaternaryQuadraticForms/QuadraticGaussShift.lean)
   implements it as a bijection on the residue vectors, using the native
   modular inverse. [IntegralGaussShift](QuaternaryQuadraticForms/IntegralGaussShift.lean)
   checks reduction of the actual adjugate dual form and gives exactly
   the source phase `-(4aα)⁻¹F*(u)`.
4. [GeneralPrimeGauss](QuaternaryQuadraticForms/GeneralPrimeGauss.lean)
   constructs an orthogonal basis for the general symmetric matrix over
   the prime field. It proves that every diagonal coefficient is nonzero
   and that their product is `det A` times the square of the actual
   change-of-basis determinant. The existing one-dimensional Gauss
   identities then give the prime base case with character `χ(p)`.
5. [PrimePowerResidues](QuaternaryQuadraticForms/PrimePowerResidues.lean)
   constructs digit bijections without any coprimality hypothesis.
   [PrimePowerGaussRecurrence](QuaternaryQuadraticForms/PrimePowerGaussRecurrence.lean)
   splits the two outer base-`p` digits, checks the quadratic phase,
   and uses additive orthogonality to retain exactly the zero low digit.
   This proves `V_{k+2}(a)=p⁴V_k(a)` for the actual Gauss sum, including
   the base modulus `p^0=1`.
6. [PrimePowerGauss](QuaternaryQuadraticForms/PrimePowerGauss.lean)
   proves the closed pure and shifted formulas for all `k≥0`, using
   `V_0=1`, the general prime base case, and `χ(p)²=1` at good primes.
   Its pure-value theorem for a residue unit retains `k≥1`: this is
   needed to deduce `p ∤ a` for the unit's canonical integer lift. At
   `k=0`, the unique residue unit has lift zero, and the separate
   modulus-one identity supplies the base value.
7. [RamanujanSums](QuaternaryQuadraticForms/RamanujanSums.lean)
   defines the actual unit sums, their integral and prime bridges, and
   their multiplication and inversion permutations, including modulus
   one. [GaussRamanujan](QuaternaryQuadraticForms/GaussRamanujan.lean)
   proves the exact negative reciprocal-phase sum. Its intermediate
   constant-Gauss hypothesis is discharged in
   [UnramifiedCompleteSum](QuaternaryQuadraticForms/UnramifiedCompleteSum.lean),
   giving the final source formula for `S_{p^k}` with no unevaluated
   Gauss identity left as an assumption.
8. [QuadricCounting](QuaternaryQuadraticForms/QuadricCounting.lean)
   expresses the actual affine zero count through additive orthogonality
   and relates its nonzero vectors to the existing projective rays.
   [QuadricPointCount](QuaternaryQuadraticForms/QuadricPointCount.lean)
   proves the affine count `p³+χ(p)(p²-p)` and the exact projective
   count, including its integer-valued source statement. The origin
   and the `p-1` nonzero representatives of each ray are accounted for.
9. [PrimePowerGaussTheorem](QuaternaryQuadraticForms/PrimePowerGaussTheorem.lean)
   combines all three conclusions in `prime_power_gauss` under the
   source symmetry, good-prime and positive-exponent hypotheses.

The [source correspondence review](certification/correspondence/prime_power_gauss.md)
records the literal matrix, sums, inverse phase, character, and actual
point sets. No diagonalization, recurrence, Gauss evaluation, unit-sum
identity or point count remains an internal assumption of the final
theorem. The 54 new public exports and 16 modules remain separate
counts from the single numbered lemma and the auxiliary-group ledger.

## Completed complete-sum bound at every positive modulus

[BadPrimeBound](QuaternaryQuadraticForms/BadPrimeBound.lean) proves the
full source endpoint `bad_prime_bound` of Lemma 3.3:

$$
\lVert S_c(u)\rVert\le4\sqrt{|\det A|}\,c^3.
$$

The sum is the existing `unweightedCompleteSum c A u`. Its hypotheses
are `[NeZero c]`, `A.transpose=A`, and `A.det≠0`, with arbitrary
`u : Fin 4 → ℤ`. Thus it covers every positive source modulus and
frequency, including modulus one, even moduli, bad-prime powers,
and mixed composite moduli. There is no good-prime, oddness,
nonzero-frequency, or nonsquare-determinant restriction.

The completed proof uses the following actual objects and deductions:

1. [GaussNorm](QuaternaryQuadraticForms/GaussNorm.lean) proves
   four-coordinate additive orthogonality at every positive modulus.
   For each actual unit parameter `a`, translation of the finite
   vector sum and symmetry of `A` give the exact identity

   $$
   V\overline V
   =c^4\sum_{\substack{z\bmod c\\2Az=0\bmod c}}
     e_c(aF(z)+u\cdot z).
   $$

   The unit `a` cancels in the linear kernel condition; the factor
   two remains in the matrix. Taking norms and using the norm-one
   character values proves `|V|²≤c⁴ #ker(2A mod c)`. This step works
   even when the reduced matrix is singular.
2. [MatrixResidueKernel](QuaternaryQuadraticForms/MatrixResidueKernel.lean)
   defines `matrixResidueKernel c B` as the literal filtered finite
   set of vectors killed by the reduction of an integer matrix `B`.
   [IntegerMatrixKernelBound](QuaternaryQuadraticForms/IntegerMatrixKernelBound.lean)
   constructs the actual coordinate-reduction homomorphism, proves
   it surjective with canonical lifts, and checks that reduction
   carries the integer matrix range onto the residue matrix range.
   For nonsingular `B`, it derives

   $$
   \#\ker(\overline B)
   =[(\mathbb Z/c\mathbb Z)^4:\operatorname{im}(\overline B)]
   \mid[\mathbb Z^4:B\mathbb Z^4]
   =|\det B|.
   $$

   The first equality is the finite-endomorphism index theorem;
   divisibility follows from the surjective reduction map. The final
   equality applies mathlib's proved determinant-index theorem to the
   actual integer matrix, whose injectivity follows from its nonzero
   determinant. Positivity then gives the public bound
   `(matrixResidueKernel c B).card ≤ B.det.natAbs`. The proof uses
   mathlib's Smith-normal-form determinant-index theorem; the new
   exported endpoint is this bound, with no separate exact
   gcd-product kernel formula claimed.
3. [DoubledMatrixKernel](QuaternaryQuadraticForms/DoubledMatrixKernel.lean)
   identifies the kernel selected by polarization with the actual
   reduction of the integer matrix `2 • A`.
   [GaussBoundConstants](QuaternaryQuadraticForms/GaussBoundConstants.lean)
   proves `det(2 • A)=16 det A` and its absolute-value identity. It
   checks the nonnegative square-root calculation giving the precise
   constant four and bounds the actual unit-group cardinality by `c`.
4. [BadPrimeGaussBound](QuaternaryQuadraticForms/BadPrimeGaussBound.lean)
   combines these deductions to prove the squared bound
   `|V|²≤c⁴(16|det A|)` and hence
   `|V|≤4√|det A| c²`. Its residue-unit endpoint covers every frequency
   modulo `c`; the integral endpoint uses the original matrix,
   integer scalar with unit reduction, and integral frequency.
5. [CompleteSumNorm](QuaternaryQuadraticForms/CompleteSumNorm.lean)
   applies the triangle inequality to the actual outer unit sum.
   Its common inner bound is an explicit hypothesis of this assembly
   helper. [BadPrimeBound](QuaternaryQuadraticForms/BadPrimeBound.lean)
   supplies that bound from the proved matrix and norm results, then
   gives the complete source estimate in both natural-absolute-value
   and real-absolute-value notation. No inner estimate or kernel
   count remains assumed in the final theorem.

The [source correspondence review](certification/correspondence/bad_prime_bound.md)
records the actual sums, the modulus-one convention, the determinant
constant, and the precise relationship to the manuscript's Smith
normal form argument. All 17 new exports in eight modules passed
strict targeted builds and actual type/axiom inspection. Each uses
exactly `Classical.choice`, `Quot.sound`, and `propext`. The four
registered literature premises and their established scopes are
unchanged. Aggregate verification and CI execution evidence are
recorded separately in the checkpoint.

## Completed shared-prime complete-sum evaluation

[RamifiedCompleteSum](QuaternaryQuadraticForms/RamifiedCompleteSum.lean)
proves the full source endpoint `source_ramified_complete_sum` of
Lemma 3.4. For the source's symmetric nonsingular integral matrix,
a source prime `p∤N` with `rad(N_F)∣N`, every exponent `k≥1`, and
every integral frequency, it gives

$$
\mathcal S_{p,p^k}(u)
=\chi(p)^{k+1}p^{2k+1}
 \xi_p(\operatorname{adj}(A)u)\,
 R_{p^{k+1}}(F^*(u)).
$$

The formula uses the existing `mixedCompleteSum`, the literal integer
dual value `F*(u)=u·adj(A)u`, the Legendre symbol `χ(p)=(det A/p)`,
and the actual Ramanujan sum over units. The proof has six steps:

1. [WeightedGaussSums](QuaternaryQuadraticForms/WeightedGaussSums.lean)
   defines `weightedIntegralGaussSum` and `primeWeightedCompleteSum`
   by the actual vector and unit sums. The local weight is evaluated
   on the reduction modulo `p` of each canonical integer vector.
   Constant weight one recovers the existing integral Gauss and
   complete sums. In particular, at modulus `p^j` the latter
   definition is exactly the source's `𝒰_j`.
2. [WeightedGaussStationaryPhase](QuaternaryQuadraticForms/WeightedGaussStationaryPhase.lean)
   reindexes vectors as `x=y+mz` at modulus `mp`, where `p∣m`.
   The phase is `aF(y)+u·y+m(2aAy+u)·z`, and the weight is unchanged
   modulo `p`. Four-coordinate additive orthogonality contributes
   `p⁴` precisely when `2aAy+u=0 mod p`, and zero otherwise.
   Taking `m=p^(j−1)` gives the source expansion for every `j≥2`.
3. [WeightedGaussExtraction](QuaternaryQuadraticForms/WeightedGaussExtraction.lean)
   multiplies the stationary equation by the actual adjugate to prove
   `adj(A)u=−(2a det A)y mod p`. Good reduction and the unit scalar
   make this multiplier nonzero. The supplied scalar invariance
   therefore identifies every surviving weight with
   `ξ_p(adj(A)u)`. Comparing with the same expansion for constant
   weight one proves the actual weighted Gauss extraction, including
   at zero frequency.
4. [WeightedCompleteSum](QuaternaryQuadraticForms/WeightedCompleteSum.lean)
   proves that the canonical integer representative of each actual
   unit modulo `p^j` is coprime to `p` when `j≥1`. It applies the
   proved extraction to every inner sum and then uses Lemma 3.2 to
   obtain `𝒰_j=χ(p)^j p^(2j) ξ_p(adj(A)u) R_{p^j}(F*(u))`
   for `j≥2`. The common-factor premise of its elementary assembly
   helper is fully discharged in this evaluation.
5. [PrimePowerUnitDigits](QuaternaryQuadraticForms/PrimePowerUnitDigits.lean)
   restricts the actual residue-digit bijection to units and proves
   the exact canonical representative `a.val+c*t.val` at modulus
   `pc` whenever `p∣c`. [RamifiedUnitLift](QuaternaryQuadraticForms/RamifiedUnitLift.lean)
   sums the scalar digit `t mod p`. Its orthogonality gives a single
   factor `p` and precisely the existing cone constraint `p∣F(x)`.
   The prime-product weight specializes to `ξ_p`, proving
   `𝒰_{k+1}=p 𝒮_{p,p^k}` for every `k≥1`. This branch requires no
   symmetry, good-reduction, or scalar-invariance hypothesis.
6. [SourceGoodPrime](QuaternaryQuadraticForms/SourceGoodPrime.lean)
   proves that the exact source condition `rad(N_F)∣N`, together
   with `p∤N`, implies `p∤N_F`. The source hypothesis `det A≠0`
   is retained: it makes `N_F=2|det A|` nonzero, which is necessary
   for the literal prime-radical membership theorem at this step.
   [RamifiedCompleteSum](QuaternaryQuadraticForms/RamifiedCompleteSum.lean)
   combines the two evaluations of `𝒰_{k+1}` and cancels only the
   proved nonzero scalar `p`, giving the exponent `2k+1`. Its source
   wrapper accepts weights only at primes not dividing `N`; it uses
   the existing total-family extension inside the mixed sum and
   proves that the right-hand weight is the original supplied function.

Only invariance under nonzero scalar multiplication is needed from
the source weight hypotheses. The conditions `ξ_p(0)=0`, the norm
bound, and the Fourier stratification estimates are not used; the
proved identity is correspondingly stronger and covers every frequency.
The global nonsquare-determinant assumption is also unnecessary.
The [source correspondence review](certification/correspondence/ramified_complete_sum.md)
records these strengthenings and every actual map and normalization.
The 18 new theorem exports in eight modules use only standard logical
foundations and add no registered literature premise. Strict targeted
builds and actual type/axiom inspection have passed; every inspected
dependency list is exactly `Classical.choice`, `Quot.sound`, and
`propext`. Aggregate verification and CI execution evidence are
recorded separately in the checkpoint.
That completed milestone covered 571 exports, 128 proof modules and
155 inspected input hashes; the current totals include Lemmas 3.5, 3.6, and 3.7.

## Completed global mixed-sum and dual-cone identities

[GoodGlobalTheorem](QuaternaryQuadraticForms/GoodGlobalTheorem.lean)
proves both clauses of Lemma 3.5 in `source_good_global_complete_sum`,
with separate source exports for each clause. The matrix is the
source's symmetric nonsingular integral matrix, `q≥1` is squarefree,
`(q,N)=1`, and `rad(N_F)∣N`. The supplied character is an actual
Dirichlet character with the good-prime Legendre values stated in
the introduction. The weights are the original functions supplied
at primes not dividing `N`, with their nonzero scalar invariance.

For every positive `c`, the factors are literally `q₁=gcd(q,c)` and
`q₂=q/q₁`. If `(c,N_F)=1`, the first clause is

$$
\mathcal S_{q,c}(u)
=C_{q_2}(u)\,q_1c^2\chi(q_1c)\,
 \xi_{q_1}(\operatorname{adj}(A)u)\,
 R_{q_1c}(F^*(u)).
$$

If `F*(u)=0`, the second clause holds for every positive `c`, including
arbitrary bad-prime factors:

$$
\mathcal S_{q,c}(u)
=C_{q_2}(u)\,q_1^2\chi(q_1)\,
 \xi_{q_1}(\operatorname{adj}(A)u)\,S_c(u).
$$

The proof uses the following actual objects and deductions:

1. [RamanujanMultiplicativity](QuaternaryQuadraticForms/RamanujanMultiplicativity.lean)
   reindexes the actual unit group by the existing scaled CRT
   equivalence and splits the standard additive character. It
   proves `R_{mn}(t)=R_m(t)R_n(t)` for coprime positive factors,
   including factors equal to one. At zero the sum is the actual
   unit-group cardinality, giving `R_n(0)=φ(n)`. The proved
   totient identity `φ(dc)=dφ(c)` whenever `d∣c` supplies the
   additional factor on the dual cone.
2. [GlobalQuadraticCharacter](QuaternaryQuadraticForms/GlobalQuadraticCharacter.lean)
   uses the actual integer Jacobi symbol cast to `ℂ`, proves its
   multiplicativity and prime-power Legendre agreement, and proves
   equality with the original supplied `DirichletCharacter ℂ M`
   at every positive modulus coprime to `N_F`. Prime induction
   establishes composite agreement from the source's given good-prime
   values; no global identity with the source character is assumed.
   No character agreement at bad, even, or zero moduli is claimed.
3. [GoodUnweightedCompleteSum](QuaternaryQuadraticForms/GoodUnweightedCompleteSum.lean)
   extends the proved prime-power formula to every positive good
   modulus by actual complete-sum CRT and Ramanujan multiplicativity.
   The modulus-one base is explicit. The result is
   `S_c(u)=χ(c)c²R_c(F*(u))` after the proved character bridge,
   for every integral frequency.
4. [SquarefreeGcdFactors](QuaternaryQuadraticForms/SquarefreeGcdFactors.lean)
   proves positivity, squarefreeness, `q₁q₂=q`, `q₁∣c`, and
   `(q₂,q₁c)=1` for the literal source factors. For coprime
   modulus factors `m,n`, a squarefree divisor of `mn` splits as
   `gcd(q,m)gcd(q,n)`, with the full resulting CRT blocks coprime.
   A squarefree divisor of a prime power is proved to be one or
   that prime, including the exponent-zero boundary.
5. [SharedSupportCompleteSum](QuaternaryQuadraticForms/SharedSupportCompleteSum.lean)
   first evaluates the mixed sum for squarefree `q∣c` at good
   positive moduli. The two prime-power cases use the actual
   unweighted formula and the completed ramified Lemma 3.4.
   Induction over coprime modulus factors splits the weight modulus
   by its actual gcds and combines the actual sums, Jacobi factors,
   supplied weights and Ramanujan sums. The resulting coefficient
   is exactly `q c² χ(qc)`.
6. [GoodGlobalCompleteSum](QuaternaryQuadraticForms/GoodGlobalCompleteSum.lean)
   separates the `q₂` block at complete-sum modulus one by actual
   CRT. This block is precisely `C_{q₂}(u)`. The shared-support
   evaluation of the remaining `q₁,c` block proves the first
   full formula with the literal gcd and quotient.
7. [ModulusPrimeSplit](QuaternaryQuadraticForms/ModulusPrimeSplit.lean)
   constructs positive coprime factors `c=c_bad*c_good`, with
   every prime of `c_bad` dividing `N_F` and `(c_good,N_F)=1`.
   It proves `(q,c_bad)=1` and
   `gcd(q,c)=gcd(q,c_good)` from `(q,N_F)=1`.
   [ConeCompleteSum](QuaternaryQuadraticForms/ConeCompleteSum.lean)
   first specializes the good formula using
   `R_{q₁c}(0)=φ(q₁c)=q₁φ(c)` and the proved formula for `S_c`.
   It then uses both actual CRT identities to multiply through
   by `S_{c_bad}(u)`. That factor is never divided out; its possible
   vanishing is included. Thus the second source clause covers
   every positive modulus, all bad-prime powers, and mixed factors.
8. [SourceGoodModulus](QuaternaryQuadraticForms/SourceGoodModulus.lean)
   derives `(q,N_F)=1` from the exact source hypotheses
   `(q,N)=1`, `rad(N_F)∣N`, and `det A≠0`. Nonsingularity makes
   the actual bad-prime modulus nonzero for the radical argument.
9. [SourceCompositeWeights](QuaternaryQuadraticForms/SourceCompositeWeights.lean)
   defines the literal product of the original supplied functions
   over the prime divisors of a modulus coprime to `N`. It proves
   equality with the existing total-family representation inside
   the complete sums. [GoodGlobalTheorem](QuaternaryQuadraticForms/GoodGlobalTheorem.lean)
   applies this weight bridge and the actual Dirichlet-character
   agreement to both clauses, then gives their bundled source endpoint.

The statements include `q=1`, `c=1`, all integral frequencies in the
first clause, and every integral point of the dual cone in the second.
The source condition `N≥1` is unused; it is not a consequence of
`(q,N)=1`, since `q=1,N=0` satisfies that coprimality condition.
Once the source character and its stated prime values are supplied,
its primitivity and the nonsquare-determinant condition are unnecessary
for these identities. Only nonzero scalar invariance is used from
the weight hypotheses; vanishing at zero, the norm bound, and the
Fourier stratification bounds are unused.

The [source correspondence review](certification/correspondence/good_global_complete_sum.md)
records both clauses, the actual sums and source-data bridges, and
these strengthenings. All 27 new theorem exports in 11 modules
passed strict targeted builds and actual type/axiom inspection.
`gcd_mul_blocks_coprime` uses only `propext`; the other 26 exports
use exactly `Classical.choice`, `Quot.sound`, and `propext`.
No registered literature premise is added or used. Aggregate
verification and CI execution evidence are recorded separately
in the checkpoint.

## Completed off-dual-cone modulus estimate

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

## Completed dual-cone modulus cancellation

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

## Continuation status

The requested **Lemma 2.3** is complete at the proof and source-review level.
The current verification block records the aggregate execution evidence.
This session stops here; no additional proof target is started.

All numbered results in Section 2 (Lemmas 2.1–2.7), Lemmas 3.1–3.11,
and all Section 4 lemmas are complete. The numbered inventory is
**25 Complete, 0 Partial, 0 Active, 17 Pending**. Supplementary groups
remain **5 Certified, 28 Pending**, including Pending **aux:conecount**.
The scaled-integral, Poisson, and three-frequency contributions and the
general cone-vertex singular-integral obligation remain for the later
analytic assembly. The global proposition and main theorems are not certified.

The graphs can be regenerated from the detailed inventory with
`python3 scripts/build_dependency_graph.py`. Graph rendering needs Graphviz;
checking the Lean proofs does not.
