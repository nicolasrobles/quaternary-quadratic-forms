# Complete local-sum CRT checkpoint

## Numbered-result status

Complete: **11**. Partial: **0**. Active numbered targets: **0**.
Pending: **31**. All 33 auxiliary/supplementary groups remain Pending.

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
tangent and singular sections. Theorem 1.1 and Theorem 1.4 remain Pending.

**Lemma 4.5 is Certified.** All three clauses are proved for the actual
diagonal forms: characteristic-zero smoothness, geometric bad reduction
at `p ∤ N_F` if and only if `p ∣ M`, and the exact formula
`N_G = rad(|2αM|)` for the existing modulus. Finiteness follows directly
from `M ≠ 0`; no Lang or other literature premise is used.

**Lemma 4.6 is Certified relative to the accepted Weil input.** Its
complete integral theorem proves the exact pencil formula, the literal
integer projective-trace identity, and the generic Fourier bound
`2p^(3/2)+4p`. The prime hypothesis is precisely `p ∤ 2αM`, and the
generic condition is precisely `p ∤ F*(u)u₁u₂u₃u₄`. The exact formula
and trace use only the standard foundations; the bound additionally uses
the existing Weil premise. All Section 4 lemmas are now complete.
Theorem 1.3 remains Pending because its global asymptotic is not proved.

**Lemma 3.1 is Certified.** The actual mixed complete sum satisfies both
the CRT factorization and integer unit-frequency invariance. Integer
lift independence, the source's prime-product weights, and the extension
of functions supplied only at primes outside `N` are proved internally.
The identities include modulus one and shared prime factors between `q`
and `c`; the literal gcd condition also permits `t=0` when `qc=1`.
The supporting prime-factor formula for `C_q`, multiplicativity of
`S_c`, and exact prime Fourier bridge are proved. No literature premise
is used. The next target is complete Lemma 3.2.

## Mathematical scope

### Complete Lemma 3.1

`CompleteSumTheorem.lean` proves `complete_sum_crt` and the final source
wrapper `source_complete_sum_crt`. They concern the existing actual
mixed sum, with the source's integral matrix and frequency and the
literal coprimality condition `(q₁c₁,q₂c₂)=1`. The source wrapper
accepts a local function only for each prime `p ∤ N`, and assumes
`(q₁q₂,N)=1`. Both conclusions are included:

$$\mathcal S_{q_1q_2,c_1c_2}(u)=
\mathcal S_{q_1,c_1}(u)\mathcal S_{q_2,c_2}(u),$$

$$\mathcal S_{q,c}(tu)=\mathcal S_{q,c}(u)
\qquad\text{for every integer }t\text{ with }\gcd(t,qc)=1.$$

`CompositeWeights.lean` defines the actual product
`ξ_q(x)=∏_{p∣q} ξ_p(x mod p)`, with `ξ_1=1`. It proves periodicity,
compatibility with residue lifts and coefficient reduction, factorization
on coprime moduli, and invariance under a unit scalar. The invariant
predicate only concerns primes dividing the specified `q`.
`SourceWeights.lean` extends the supplied good-prime family by zero at
other indices and proves that this extension agrees with every factor
used when `(q,N)=1`. No property at an excluded prime is assumed.

`CompleteSums.lean` defines `mixedCompleteSum`,
`unweightedCompleteSum`, and `constrainedFourierSum` as their literal
finite sums. The mixed sum is over units modulo `c` and vectors modulo
`qc`, constrained by `q ∣ F(x)`, with phase `e_{qc}(aF(x)+u·x)`.
The quadratic value is `dotProduct x (A.mulVec x)`, proved equal to
evaluation of the actual matrix quadratic polynomial.

The canonical representatives in the definition introduce no extra
choice hypothesis. Changing a vector lift modulo `qc` preserves the
weight, congruence condition, and phase. Changing the representative
of `a mod c` changes `aF(x)` by a multiple of `qc`, because the summation
condition is `q ∣ F(x)`. The mixed-phase proof checks this divisibility
before applying the actual standard additive character.

`CRTArithmetic.lean` builds actual residue, unit, and vector bijections
from mathlib's Chinese remainder equivalence. Their forward maps are
the source's scaled coordinates `x=n₂x₁+n₁x₂` and
`a=c₂a₁+c₁a₂`, where `n_i=q_i c_i`. `CRTCharacters.lean` proves
`e_{mn}(nz)=e_m(z)` and
`e_{mn}(na+mb)=e_m(a)e_n(b)` for positive arbitrary moduli, including
one. `MixedPhase.lean` proves the exact source quadratic phase split.
`CompleteSumCRT.lean` combines these with the prime-product weight and
the quadratic-congruence split, then reindexes the local units by
`c₂n₂` and `c₁n₁` to prove the actual double-sum product.

The required coprimality is between the two complete CRT blocks.
There is no assumption `(q,c)=1`; a prime may divide both `q_i` and
`c_i` within a block. The argument in fact needs neither squarefreeness
nor nonsingularity for the two main identities. The source's additional
hypotheses therefore specialize the proved theorem without adding an
unproved implication.

`CompleteSumInvariance.lean` proves the second clause by reindexing
vectors with an inverse of `t` modulo `qc` and units with multiplication
by `t²` modulo `c`. Its final hypothesis is exactly
`t.gcd ((q*c : ℕ) : ℤ)=1`. Negative scalars are included. At modulus
`qc=1`, the residue and unit types are singletons, the sum equals one,
and the same gcd condition permits `t=0`. No global assumption
`t ≠ 0` is introduced.

`CompleteSumSpecializations.lean` proves
`𝒮_{1,c}=S_c`, `𝒮_{q,1}=C_q`, and
`C_1=S_1=𝒮_{1,1}=1`. Its prime theorem identifies `C_p` with the
actual sum on the finite-field quadratic cone. For a polynomial-character
weight, this is exactly the already checked `integralFourierSum`, with
matching coefficients, frequency, and standard additive character. The
bridge itself needs no homogeneity or character-order hypothesis.

`CompleteSumFactorization.lean` proves multiplicativity of `S_c` in
coprime moduli and the squarefree formula

$$C_q(u)=\prod_{p\mid q}C_p(u).$$

The finite-product induction uses invariance only at primes dividing
`q`, and the empty product handles `q=1`. These remain supporting
exports; the separate auxiliary groups are not thereby certified.
The [source correspondence review](certification/correspondence/complete_sum_crt.md)
records both source clauses, the representative choices, modulus-one
cases, source-family extension, and exact connection to the earlier
Fourier branch. All 66 new exports use only standard Lean foundations.

### Complete Lemma 4.6

`DiagonalPencilTheorem.lean` proves the final all-clauses theorem
`diagonal_pencil` for integral vectors `a,b,u` under the literal hypothesis
`¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b`. The actual
sum is the existing `integralFourierSum` for `Matrix.diagonal a`, the
complex quadratic character, and the polynomial of `Matrix.diagonal b`.
The statement reduces the formal integral `Φ_u` polynomial and the
integral `κ_i,ν_i` values into `ZMod p`; its singular filter uses literal
integer divisibility `p ∣ u_i`.

The exact formula is

$$C_p(u)=p\sum_{t\notin\{t_1,t_2,t_3,t_4\}}\chi_p(-\Phi_u(t))
 +p\sum_{i:\,p\mid u_i}\chi_p(\kappa_i)R_p(\nu_i(u)).$$

`DiagonalPencil.lean` defines the source's actual pencil data, including
`κ_i = −a_i ∏_{j≠i}(a_i b_j−a_j b_i)`, and proves their compatibility
with coefficient maps. `DiagonalPencilCubic.lean` identifies the cubic
coefficient with evaluation of the actual adjugate matrix polynomial
and identifies `Φ_u(t)` with the dual form of `G+tF`.
`DiagonalPencilAlgebra.lean` proves distinctness of the four singular
parameters, deduces `5 ≤ p`, and proves the regular and singular
identities. In particular,
`−Δ_i = κ_i/a_i⁴` and `w_i = ν_i/(a_i²Δ_i)` have their literal source
signs and denominators.

`PrimeQuadraticGauss.lean` derives the scalar prime-field identities
from proved mathlib Gauss-sum and square-root counting results. Its
exports cover nonvanishing of `τ_p`, `τ_p²=χ_p(−1)p`, `τ_p⁴=p²`,
Gauss inversion including zero, inversion over units, and the two
square-completion branches. `PrimeRamanujan.lean` defines the actual
finite sum and proves its values `p−1` and `−1`, together with the
unit-scaling and reciprocal-parameter invariances. These statements
use no registered external premise.

`FourierOrthogonality.lean` and `FourierGaussExpansion.lean` express
the actual constrained Fourier sum as the product of four scalar
quadratic exponential sums. The Gauss parameter is a unit before the
substitution `v=s t` or inversion. `DiagonalPencilEvaluation.lean`
computes every regular and singular contribution.
`DiagonalPencilFormula.lean` splits the finite parameter set and
cancels the nonzero factor `p τ_p` to prove the exact formula. Singular
terms with `ν_i(u)=0` remain present; no uniform size-`p` assertion is
made for those terms.

At zero frequency, the regular contribution vanishes and every
Ramanujan value is `p−1`. `DiagonalPencilConsequences.lean` combines
this with the existing exact zero-frequency identity and cancels
`p−1` to obtain the actual complex trace and integer trace. The final
integral identity is

$$a_p(G)=p\sum_i\chi_p(\kappa_i).$$

For the generic bound, `DiagonalPencilReduction.lean` derives all
nonzero coordinate and dual-value hypotheses from
`p ∤ F*(u)u₁u₂u₃u₄`, where `F*(u)` is the actual integral adjugate
quadratic value. The singular sum is empty and `Φ_u` has degree three.
`CubicCharacterSum.lean` handles the separable case using the existing
Weil premise. Over the perfect prime field, a nonseparable cubic is
factored as `c (X−a)²(X−b)` and its actual sum is evaluated internally.
Thus no separability hypothesis is added. The sum over all parameters
has norm at most `2√p`; deleting four parameters gives `2√p+4`, and
multiplication by `p` gives the literal source bound

$$|C_p(u)|\le2p^{3/2}+4p.$$

The four exports in `DiagonalPencilTheorem.lean` give the integral exact
formula, integral projective trace, generic estimate, and conjunction
of all clauses. The formula and trace use only `Classical.choice`,
`Quot.sound`, and `propext`. The generic estimate and all-clauses theorem
add only `QuaternaryQuadraticForms.Trusted.weil_simple_roots`; they use
no Katz, Lang, or Bertini premise. The
[source correspondence review](certification/correspondence/diagonal_pencil.md)
records the full source match. This completes all Section 4 lemmas;
the global asymptotic in Theorem 1.3 remains Pending.

### Complete Lemma 4.5

`DiagonalBadPrimes.lean` proves the final all-clauses theorem
`diagonal_bad_primes`. The integral coefficient vectors `a,b` define
`A = Matrix.diagonal a` and the actual polynomial of `Matrix.diagonal b`.
The hypotheses are `α = ∏ i, a_i ≠ 0` and
`a_i b_j − a_j b_i ≠ 0` for each of the six pairs `i < j`.
`DiagonalForms.lean` proves the formal polynomial identity with
`∑ i, C(a_i) X_i²`, defines the literal product `M`, and proves the
required coefficient-map, nonvanishing, and sign identities.

`DiagonalGeometry.lean` calculates the actual gradient rows and their
two-by-two minors `4 x_i x_j (a_i b_j − a_j b_i)`. In a field of odd
characteristic with nonzero `a_i`, pairwise nonzero determinants imply
the geometric rank-two condition. If the rank failed, the minors would
force at most one nonzero coordinate, contrary to `F(x)=0`.

Conversely, when a pair determinant vanishes, the proof constructs an
actual nonzero point over the algebraic closure: `x_i=1`,
`x_j²=−a_i/a_j`, and all other coordinates zero. An algebraic-closure
square root supplies the coordinate. Both defining polynomials vanish,
and the actual gradient rows are proportional, so their rank is not two.
This establishes the exact field criterion, rather than assuming a
geometric singularity from a numerical surrogate.

`DiagonalReduction.lean` maps the actual equations to the algebraic
closures of `ℚ` and `ZMod p`. It proves `SmoothCharacteristicZero` from
the integral hypotheses and derives odd characteristic and nonzero
reduced `a_i` directly from `p ∤ N_F`. The resulting equivalence is

$$\neg\operatorname{GoodReductionAt}(p,A,G)
\quad\Longleftrightarrow\quad p\mid M
\qquad(p\nmid N_F).$$

The primewise theorem does not additionally assume integral `M ≠ 0`.
It includes `p=3`, zero coefficients `b_i`, and arbitrary signs of the
integer data. No `p ≥ 5` condition enters Lemma 4.5.

`BadPrimeRadical.lean` derives finiteness of the existing bad-prime set
from a nonzero integer with this exact divisibility criterion. Its actual
finset is `primeFactors(|M|) ∖ primeFactors(N_F)`. The disjoint union
with the prime factors of `N_F` therefore proves
`polynomialBadPrimeModulus = primeRadical(N_F * |M|)`. Shared prime
divisors occur once, without a coprimality assumption.

The final diagonal wrapper supplies `M ≠ 0` from the six source hypotheses
and proves the literal identity

$$N_G=\operatorname{rad}(|2\alpha M|).$$

`diagonal_badPrimeModulus` holds for any proof of finiteness passed to
the existing modulus. `diagonal_bad_primes` supplies that proof internally
and combines the smoothness, primewise criterion, and modulus equality.
All 24 new exports have only `Classical.choice`, `Quot.sound`, and
`propext` among their inspected axioms. In particular, the direct
finiteness argument uses no Lang elimination premise. The
[source correspondence review](certification/correspondence/diagonal_bad_primes.md)
records the hypotheses, algebraic-closure witness, signs, and all three clauses.

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

- [Complete Lemma 3.1 and its source-family wrapper](QuaternaryQuadraticForms/CompleteSumTheorem.lean).
- [Actual complete sums and lift independence](QuaternaryQuadraticForms/CompleteSums.lean).
- [Mixed CRT factorization](QuaternaryQuadraticForms/CompleteSumCRT.lean).
- [Literal unit-frequency invariance](QuaternaryQuadraticForms/CompleteSumInvariance.lean).
- [Source weight family outside the excluded primes](QuaternaryQuadraticForms/SourceWeights.lean).
- [Modulus-one identities and exact prime Fourier bridge](QuaternaryQuadraticForms/CompleteSumSpecializations.lean).
- [Prime factorization and unweighted multiplicativity](QuaternaryQuadraticForms/CompleteSumFactorization.lean).
- [Complete local-sum CRT correspondence review](certification/correspondence/complete_sum_crt.md).
- [Complete integral Lemma 4.6](QuaternaryQuadraticForms/DiagonalPencilTheorem.lean).
- [Exact finite-field pencil formula](QuaternaryQuadraticForms/DiagonalPencilFormula.lean).
- [Trace and generic Fourier bound](QuaternaryQuadraticForms/DiagonalPencilConsequences.lean).
- [Scalar prime Gauss identities](QuaternaryQuadraticForms/PrimeQuadraticGauss.lean).
- [Literal prime Ramanujan sums](QuaternaryQuadraticForms/PrimeRamanujan.lean).
- [Cubic estimates with repeated roots](QuaternaryQuadraticForms/CubicCharacterSum.lean).
- [Complete diagonal-pencil correspondence review](certification/correspondence/diagonal_pencil.md).
- [Complete Lemma 4.5 and its exact modulus](QuaternaryQuadraticForms/DiagonalBadPrimes.lean).
- [Literal diagonal data and six-factor product](QuaternaryQuadraticForms/DiagonalForms.lean).
- [Diagonal rank criterion and geometric singular point](QuaternaryQuadraticForms/DiagonalGeometry.lean).
- [Characteristic-zero and prime reduction wrappers](QuaternaryQuadraticForms/DiagonalReduction.lean).
- [Direct bad-prime finiteness and radical formula](QuaternaryQuadraticForms/BadPrimeRadical.lean).
- [Complete diagonal bad-prime correspondence review](certification/correspondence/diagonal_bad_primes.md).
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

The current CRT milestone contains 482 theorem exports across 96 project
Lean modules and 20 mapped source groups: 66 new exports in 12 new
modules. The four registered literature premises and all nine pinned
dependency revisions are unchanged. Source groups and Lean premise
declarations remain separate counts. The completed aggregate report
records 120 input hashes, including the new correspondence review.

All 12 new modules have passed strict builds under official Lean 4.24.0
and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 66 new actual theorem types and axiom lists
have been inspected. Exactly 65 use `Classical.choice`, `Quot.sound`,
and `propext`; `residueLift_cast` uses only `Quot.sound` and `propext`.
No new theorem uses a registered literature premise. The frozen
manuscript, PDF, and dependency pins remain unchanged.

**The full aggregate local verifier passed for all 96 modules and 482
theorem exports.** All 120 input hashes match the checked files. The
independent baseline comparison confirms that all 416 preceding complete
theorem records are identical, including actual types, axiom dependencies,
source hashes, and scopes. All four registered premise records and all
nine dependency revisions match the preceding report exactly. The 66
new actual theorem types and axiom dependencies match their prior
individual inspections, with no literature premise in any new export.

All 33 changed-file hashes matched the frozen snapshot throughout the
verification run. The 13 added inspected inputs are the 12 new Lean
modules and the source correspondence review. The frozen manuscript
and PDF remain byte-for-byte unchanged. The subsequent README and
checkpoint edits record the successful execution; the inspected proof
inputs remain those checked by the aggregate verifier.

The [local verification report](certification/verification_report.json)
contains 708,765 bytes and has SHA-256
`ec46cb57a7912faf2116faed95bc6021ed68a9ed78cfb28a05133c0df4515f0f`.
It records 11 Certified and 31 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### CRT GitHub execution

**The full local and GitHub verifiers passed for all 96 modules, 482 theorem
exports, four registered premise records, and nine pinned dependency
revisions.** The published proof commit is
[`0224dae194b48080f8af732dbf78580ffaab0c24`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/0224dae194b48080f8af732dbf78580ffaab0c24),
whose tree is `62ac309aaa1aec3563b46f87e4a881d17a9bc474`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43626335642, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43626335642).
- Verification job: `132542869983`; every step succeeded.
- Verification completed `2026-11-14T18:31:45Z`; the job completed `2026-11-14T18:31:47Z`.
- Artifact: `14127140616`, 82,657 bytes, created `2026-11-14T18:31:46Z`.
- [Preserved CI report](certification/ci/run_43626335642_attempt_1.json), 715,749 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43626335642_attempt_1.zip).
- ZIP SHA-256: `7f343e481201ecbd5d9759d0c97392d0a9104db7894c05226b0dd1d19c8344e3`.
- CI report SHA-256: `72cb4961d00501e3e98a17a1871169548b7d8d70a7f479e9304bd0887a75b56b`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON. The local and CI reports agree exactly on all 18
verification-content fields: all 482 complete theorem records and their
actual types and axiom dependencies, four registered-premise records,
120 input hashes, nine pinned dependency revisions, the complete Lean
export-inspection output, the Lean version, and every verification flag
and scope count. Only `generated_at_utc` and `lake_build_output` differ.

Every recorded input hash matches both the current inspected files and
the exact proof tree. The local report remains the 708,765-byte report
identified above, byte-identical to the report in that proof commit.
The frozen manuscript and PDF are unchanged. This evidence covers the
complete current 482-export CRT milestone; the earlier local and CI
reports below retain their original scopes. The numbered-result status
remains 11 Certified, zero Partial or Active, and 31 Pending, with all
33 auxiliary/supplementary groups Pending and whole-paper certification
false.

## Earlier checked checkpoints

### Pencil local execution

The preceding pencil milestone contained 416 theorem exports across 84
project Lean modules and 20 mapped source groups: 67 new exports in 13
new modules. The four registered literature premises are unchanged,
as are all nine pinned dependency revisions. Source groups and Lean
premise declarations remain separate counts. The completed aggregate
report records 107 input hashes, including the new correspondence review.

All 13 new modules passed strict builds under official Lean 4.24.0
and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 67 new actual theorem types and axiom
dependencies were inspected. Of these, 59 use exactly
`Classical.choice`, `Quot.sound`, and `propext`; one uses only `propext`;
and seven additionally use the existing registered Weil premise.
The exact pencil formula and both complex and integer trace identities
use only standard foundations. The generic bound adds only Weil.
No new external premise has been introduced, and the Lean, mathlib,
manuscript, and PDF inputs remain fixed.

**The full local and GitHub verifiers passed for all 84 modules, 416 theorem
exports, four registered premise records, and nine pinned dependency
revisions.** All 107 input
hashes match the checked files. The independent baseline comparison
confirmed that all 349 preceding complete theorem records are unchanged,
including their actual types, axiom lists, source hashes, and scopes.
All four registered premise records and all nine dependency revisions
also match the preceding report exactly. The 67 new actual types and
axiom lists match their earlier individual inspections.

At the verification freeze, all 34 changed-file hashes matched the frozen
snapshot. The 14 added inspected inputs are the 13 new Lean modules and
the new source correspondence review. Among the preceding inspected
inputs, only the root Lean imports, `Checks/Exports.lean`,
`certification/status.json`, and `certification/dependency_inventory.json`
changed. The frozen manuscript and PDF remain byte-for-byte unchanged.
The subsequent edits record this successful execution in README and this
checkpoint and preserve the exact report; the inspected proof inputs
remain those checked by the successful aggregate run.

The [local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/7da6aca687135b7c0f859873e69d5fe844b2cdac/certification/verification_report.json)
contains 620,000 bytes and has SHA-256
`d60c7a129061c59979ff52a1b79adca054ed97073fd0a527eb0a6d0663a1dca1`.
It records 10 Certified and 32 Pending numbered results, with zero
Partial or Active results. All 33 auxiliary/supplementary groups remain
Pending, and whole-paper certification remains false.

### Pencil GitHub execution

The published proof commit is
[`7da6aca687135b7c0f859873e69d5fe844b2cdac`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/7da6aca687135b7c0f859873e69d5fe844b2cdac),
whose tree is `c78fd84236351f88baabd440f99fc5ca83fd2fc3`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43618745198, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43618745198).
- Verification job: `132519443067`; every step succeeded.
- Verification completed `2026-11-14T17:07:53Z`; the job and run completed `2026-11-14T17:07:56Z`.
- Artifact: `14123891609`, 72,429 bytes, created `2026-11-14T17:07:54Z`.
- [Preserved CI report](certification/ci/run_43618745198_attempt_1.json), 626,114 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43618745198_attempt_1.zip).
- ZIP SHA-256: `f2ff89bd98196e6af865a617631c6a5ee2163c984e78d4834ea56871de895407`.
- CI report SHA-256: `ba6f569e5bd2e93e6893034f2cd514779fd92536479d91ecac4e548ad0754b8c`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, byte-identical to the
archived CI JSON. The local and CI reports agree exactly on all 18
verification-content fields: all 416 complete theorem records and their
actual types and axiom dependencies, four registered-premise records,
107 input hashes, nine pinned dependency revisions, the complete Lean
export-inspection output, the Lean version, and every verification flag
and scope count. Only `generated_at_utc` and `lake_build_output` differ.

Every recorded input hash matched both the inspected files at that
checkpoint and the exact proof tree. Its proof sources, registries, source
reviews, and local report were byte-identical to the checked proof commit.
This evidence covers the complete preceding 416-export pencil milestone;
it does not cover the new 482-export CRT scope. The older local and CI
reports below retain their original scopes.


### Diagonal bad-prime local execution

The preceding diagonal bad-prime milestone registered 349 theorem exports across 71 project
Lean modules and 20 mapped source groups. The four registered literature
premises are unchanged, as are the nine pinned dependency revisions.
Source groups and Lean premise declarations remain separate counts.

Its five new modules passed strict builds under official Lean 4.24.0
and the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. All 24 new actual theorem types and axiom dependencies
were inspected. They use only the standard foundations
`Classical.choice`, `Quot.sound`, and `propext`; no new external premise is
introduced, and the diagonal finiteness proof does not use elimination.

The full aggregate local verifier passed for all 71 modules, 349 theorem
records, four registered literature-input records, and nine pinned
dependency revisions. All 93 recorded input hashes matched the files
checked. Every one of the 325 previously checked theorem records is
unchanged, including the actual types, axiom lists, source hashes and
scopes. The four registered premise records and all dependency revisions
exactly match the preceding local report. The frozen manuscript and PDF
remain unchanged.

The [local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6/certification/verification_report.json)
has SHA-256
`50606c6ea147df96a5905de201f9263396e037299d8ef3a1743c6d325d81a0b8`
and contains 525,699 bytes. It records 9 Certified and 33 Pending numbered
results, with zero Partial or Active results. All 33 auxiliary/supplementary
groups remain Pending, and whole-paper certification remains false.

### Diagonal bad-prime GitHub execution

The published proof commit is
[`09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/09d7ea0c1d2ce193be6bfc9ee7c6bea62f90cea6),
whose tree is `1930ec532bb7f03a949da69bc49cafb78634c380`.
The same verifier succeeded in the independent GitHub execution.

- [Successful run 43614640507, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43614640507).
- Verification job: `132506910704`; every step succeeded.
- Verification completed `2026-11-14T16:24:34Z`; the job completed `2026-11-14T16:24:36Z`.
- Artifact: `14121901170`, 62,602 bytes, created `2026-11-14T16:24:34Z`.
- [Preserved CI report](certification/ci/run_43614640507_attempt_1.json), 530,824 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43614640507_attempt_1.zip).
- ZIP SHA-256: `a6ee78b674f2eb0d813e442e67b5d4d0ebac91ae98e26f2d9453db7c1b54dcc9`.
- CI report SHA-256: `a9ca9c083e737b48257fbc01c3225782b61608e4a0ccc932de1d47e6d122cacd`.

The original ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, and both archived files
are byte-identical to the download and extracted member. The CI and
local reports agree exactly on all 18 verification-content fields:
all 349 full theorem records and their actual types and axiom dependencies,
all four registered-premise records, all 93 input hashes, all nine pinned
dependency revisions, the complete Lean export-inspection output, the
Lean version, and all verification flags and scope counts. The only
differing fields are `generated_at_utc` and `lake_build_output`.

Every recorded input hash also matches the files at the proof commit and
the checked source at that checkpoint. All 24 new export records have only
`Classical.choice`, `Quot.sound`, and `propext` in their axiom lists.
This evidence covers the complete 349-export diagonal bad-prime milestone.
It does not cover the new 416-export pencil scope. The older runs below
retain their original scopes.

### Polynomial Fourier local execution

The preceding polynomial Fourier milestone registered 325 theorem exports across 66 project
Lean modules and 20 mapped source groups. There are four separately
registered external Lean premises: Weil, the composite Katz/Fulton
spectral interface, Lang's general resultants, and the composite Bertini
and projective-Jacobian tangent interface. Source groups and Lean premise
declarations are counted separately.

Its seven new modules passed strict builds under official Lean 4.24.0 and
the pinned mathlib revision, with `warningAsError=true` and
`autoImplicit=false`. The final uniform wrapper compiled successfully
without additional assumptions. All 23 new actual theorem types and axiom
dependencies were inspected. Seventeen new helpers use only the
standard foundations `propext`, `Classical.choice`, and `Quot.sound`.
The generic and finite-field indicator bounds use Katz and Weil; the
zero-frequency and nonzero-frequency bounds use Katz. The integral
`fourier_bound` uses Katz, Lang, and Weil. The final
`uniform_polynomial_fourier_bound` uses all four unchanged registered
literature premises, including the construction of its exceptional
polynomial.

The full aggregate local verifier passed for all 66 modules, 325 theorem
records, four registered literature-input records, and nine pinned
dependency revisions. All 87 recorded input hashes matched the files checked
at that checkpoint. Every one of the 302 previously checked theorem types
and axiom lists was unchanged; their source hashes and scopes were also
unchanged. The four registered premise records and all dependency revisions
exactly matched the preceding local report. The frozen manuscript and PDF
were unchanged.

The [local verification report at the checked proof commit](https://github.com/nicolasrobles/quaternary-quadratic-forms/blob/25dea299d18e2a423404488ac1a923fded0cde7b/certification/verification_report.json)
has SHA-256
`88f51797dd5b426549a351f4cbc62dc24dd51b5d5c57005298b6ee691edcd003`.
The report records 8 Certified and 34 Pending numbered results, with zero
Partial or Active results; all 33 auxiliary/supplementary groups remain
Pending. Whole-paper certification remains false.

### Polynomial Fourier GitHub execution

The same verifier succeeded at exact proof commit
[`25dea299d18e2a423404488ac1a923fded0cde7b`](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/25dea299d18e2a423404488ac1a923fded0cde7b),
whose tree is `0329196f131b11b8d416917ff417c4ceb90578b1`.

- [Successful run 43611293071, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43611293071).
- Verification job: `132496696818`; every step succeeded.
- Artifact: `14120945036`, 58,271 bytes, created `2026-11-14T15:44:27Z`.
- [Preserved CI report](certification/ci/run_43611293071_attempt_1.json), 492,952 bytes.
- [Preserved original artifact ZIP](certification/ci/run_43611293071_attempt_1.zip).
- ZIP SHA-256: `e2e4750b08ac9687568d726fe155f7a409573c1b71254b1b6f9edd26190cede7`.
- CI report SHA-256: `482496c1212f5d366ebf1d54f8fd223bc58aa7cadf464582250931b60a6c060a`.

The downloaded ZIP's digest matches GitHub's advertised artifact digest.
Its sole member is `verification_report.json`, and both archived files are
byte-identical to the download and extracted member. The CI and local
reports agree exactly on all 18 verification-content fields: all 325 full
theorem records and their actual types and axiom dependencies, all four
registered-premise records, all 87 input hashes, all nine pinned dependency
revisions, the complete Lean export-inspection output, the Lean version,
and all verification flags and scope counts. The only differing fields are
`generated_at_utc` and `lake_build_output`.

Every recorded input hash also matched the files at that proof commit.
This preserved evidence covers the original 325-export scope and its eight
certified numbered results, before the diagonal milestone. The preserved
earlier runs below retain their original scopes; whole-paper certification
remains false.

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

Complete Lemma 3.2 is the next target. It has three separate conclusions
for the actual nonsingular symmetric integral quadratic form, a prime
`p ∤ N_F`, and `k ≥ 1`:

1. Evaluate the actual sum over `(ZMod (p^k))⁴` for every integer `a`
   with `p ∤ a`, including the phase
   `e_{p^k}(−(4aα)⁻¹ F*(u))` and coefficient `χ(p)^k p^(2k)`.
2. Deduce the exact formula
   `S_{p^k}(u)=χ(p)^k p^(2k) R_{p^k}(F*(u))` for the existing
   unweighted complete sum and the actual Ramanujan unit sum.
3. Prove the projective-quadric cardinality
   `p²+(1+χ(p))p+1` over the prime field.

First carry out square completion with the actual adjugate matrix over
`ZMod (p^k)`, using the good-prime hypothesis to construct the necessary
units. Prove the recurrence `V_k=p⁴V_{k−2}` with `V_0=1` by the
literal residue decomposition and additive orthogonality. The prime
base case must cover a general matrix, with diagonalization preserving
the determinant up to a nonzero square. The scalar prime Gauss identities
proved for Lemma 4.6 supply the one-dimensional calculation.

Summing over the unit parameter and its inverse gives the Ramanujan
formula. At `k=1`, orthogonality gives the affine zero count; removing
the origin and using the checked projective-ray correspondence gives
the exact projective count. None of these remaining full prime-power
or general-matrix clauses is yet recorded as Certified.

Lemma 3.1 and all Section 4 lemmas are complete. Theorem 1.3 remains
Pending because its global asymptotic is not proved. The analytic
assembly, Theorems 1.1 and 1.4, and all 33 auxiliary/supplementary groups
remain Pending.
