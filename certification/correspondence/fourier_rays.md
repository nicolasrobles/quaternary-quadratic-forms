# Source correspondence: Lemma 4.4

## Scope and source

This review covers every clause of Lemma 4.4: the three properties of the
polynomial character weight in equation (3.1), the Fourier bound involving
the exceptional polynomial `D_p`, and the exact zero-frequency identity.
It also reviews the supporting ray identity (4.5), the exceptional-section
count, and the uniform choice of `D_p` supplied by the proved Lemma 4.1(ii).
The original weight and ray analysis is retained below, followed by the
completed estimate and its source correspondence.

The source is the frozen manuscript,
[quadratic_character_sums_github.tex](../../manuscript/quadratic_character_sums_github.tex),
whose SHA-256 is
`d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33`.
The labels and numbers below agree with `certification/source.json`.

| Source location | Content reviewed | Principal Lean declarations |
| --- | --- | --- |
| `eq:forms`, (1.1), lines 157–161 | `F(x) = xᵀ A x` | `quadraticValue`, `integralFourierSum` |
| Section 1.4, lines 561–574 | Four coordinates, dot product, positive exponential convention, characters extended by zero | `PrimeVector`, `dotProduct`, `ZMod.stdAddChar`, `MulChar` |
| `eq:weightproperties`, (3.1), lines 1002–1005; proof at lines 1811–1813 | Zero at the origin, absolute value at most one, invariance under nonzero scaling | `polynomialCharacterWeight_properties` |
| `eq:Cpsi`, (4.1), lines 1595–1608 | The actual finite-field Fourier sum | `fourierSum`, `integralFourierSum` |
| `eq:rays`, (4.5), lines 1813–1822 | Both frequency cases of the ray identity | `fourierSum_ray_identity`, `integralFourierSum_ray_identity`, `integralFourierSum_of_dvd` |
| `lem:fourier`, Lemma 4.4; exact clause of `eq:fourier`, (4.4), line 1806 | `C_p(0) = (p-1)a` | `fourierSum_zero` |
| Proof of Lemma 4.4, lines 1833–1842 | Every nonzero plane section has at most `2p+2` rational points | `planeSection_card_le`, `projectiveSectionTrace_norm_le` |
| `eq:fourier`, (4.4), lines 1803–1805; proof at lines 1823–1847 | Pointwise bound with the exact constant `2n²` and exceptional-set indicator | `fourierSum_bound_prime_field`, `fourier_bound` |
| Lemma 4.1(ii), lines 1623–1630, and the opening hypotheses of Lemma 4.4, lines 1797–1800 | One uniformly bounded exceptional polynomial, independent of the character | `uniform_polynomial_fourier_bound` |

Equation (3.1) is an assumption on arbitrary functions in Section 3. The
formalized result verifies that assumption for the Section 4 specialization
`ξ_p(x) = ψ(G(x))`. It does not assert that an arbitrary function on the vector
space has those properties.

## The objects in the formal statements

The implementation of the weight properties and ray identity is in
[PolynomialWeights.lean](../../QuaternaryQuadraticForms/PolynomialWeights.lean),
[FiniteCharacters.lean](../../QuaternaryQuadraticForms/FiniteCharacters.lean),
[ProjectiveRays.lean](../../QuaternaryQuadraticForms/ProjectiveRays.lean), and
[FourierRays.lean](../../QuaternaryQuadraticForms/FourierRays.lean). The previously
checked [RayAlgebra.lean](../../QuaternaryQuadraticForms/RayAlgebra.lean) performs
the final finite-sum rearrangement.

`PrimeVector p` is `Fin 4 → ZMod p`. The hypothesis `[Fact p.Prime]` makes the
coefficient ring the field with `p` elements. `quadraticValue A x` is literally
`dotProduct x (A.mulVec x)`, with a `4 × 4` matrix over that field. Thus the
summation condition is the reduction of the manuscript's matrix expression
`xᵀ A x = 0`.

`G` is an actual `MvPolynomial (Fin 4) (ZMod p)`, with the hypothesis
`G.IsHomogeneous n`. The weight is defined by

```lean
polynomialCharacterWeight ψ G x = ψ (MvPolynomial.eval x G)
```

The character has type `MulChar (ZMod p) ℂ`. Mathlib's convention agrees with
the manuscript: every such character has value zero at zero. The identity
element `1` of the character group is the principal character, equal to one
on units and zero at zero. Consequently `ψ ^ n = 1` expresses precisely the
condition that `ψ^n` is principal; it does not incorrectly give the principal
character the value one at zero. The proof uses `MulChar.map_zero` and
`MulChar.one_apply_coe` at these two distinct places.

The additive phase is `ZMod.stdAddChar (dotProduct u x)`. Its normalization is
fixed by mathlib's theorem `ZMod.stdAddChar_coe`: on an integer `j` its value is
`Complex.exp (2 * π * I * j / p)`. This is the positive-exponent convention
`e_p(j)` at manuscript line 564.

The integral wrapper accepts the manuscript's actual integer data:
`A : Matrix (Fin 4) (Fin 4) ℤ`, `G : MvPolynomial (Fin 4) ℤ`, and
`u : Fin 4 → ℤ`. It reduces the coefficients with `Int.castRingHom (ZMod p)`
and reduces the frequency coordinatewise. `homogeneous_reduce_mod` proves
homogeneity after coefficient reduction. `reduceFrequency_eq_zero_iff` proves
that the reduced vector is zero exactly when `p` divides every integer
coordinate. Thus the two uses of `p ∣ u` and `p ∤ u` in (4.5) have the intended
meaning.

## Projective points and independence of representatives

`PrimeProjective p` is mathlib's `Projectivization (ZMod p) (PrimeVector p)`.
This is the quotient of nonzero vectors by multiplication by field units.
`projectiveQuadric A` filters these projective points by
`quadraticValue A P.rep = 0`. It therefore represents the concrete projective
zero set used in the definition of `Q(F_p)` at manuscript lines 947–949. The
finite sums do not require a scheme structure or a smoothness theory; neither
is asserted to have been formalized by this construction.

The two traces are literal sums over this zero set:

```text
projectiveTrace        = sum over F(P) = 0 of ψ(G(P.rep))
projectiveSectionTrace = sum over F(P) = 0 and u·P = 0 of ψ(G(P.rep))
```

The chosen representative is mathlib's `P.rep`. All three ingredients are
proved independent of this choice:

| Ingredient | Checked correspondence declaration |
| --- | --- |
| `F(P) = 0` | `mem_projectiveQuadric_mk`, using `quadraticValue_units_zero_iff` and `cone_rep_mk` |
| `u·P = 0` | `hyperplane_rep_mk`, using `dotProduct_units_smul_zero_iff` and `cone_rep_mk` |
| `ψ(G(P))` | `projectiveWeight_rep_mk`, using `polynomialCharacterWeight_units_smul` and `invariant_rep_mk` |

The polynomial value `G(P.rep)` itself need not be independent of the
representative. The descended quantity is its character value. The proof of
that fact uses both homogeneity and `ψ ^ n = 1`, exactly as in the paper.

`projectiveSectionTrace` is also defined at `u = 0`. In this case every point
satisfies the linear condition, and `projectiveSectionTrace_zero` proves that
it equals `projectiveTrace`. This extends the paper's notation `a_u`, which
was introduced only for a nonzero frequency, by the natural value `a_0 = a`.

## What the proofs establish

The proof of the weight properties begins with
`homogeneous_eval_smul`. It proves

$$
G(tx)=t^nG(x)
$$

from the monomial expansion of the homogeneous multivariate polynomial.
Homogeneity of the evaluation function is therefore a deduction. For positive
`n`, `homogeneous_eval_zero` gives `G(0) = 0`; character zero-extension gives
`ξ_p(0) = 0`. Multiplicativity and `ψ ^ n = 1` give scaling invariance, including
at zeros of `G`. The bound `‖ξ_p(x)‖ ≤ 1` is supplied by the established mathlib
bound for complex-valued characters. On `ℂ` this norm is the absolute value
used in (3.1). `polynomialCharacterWeight_properties` packages all three
clauses with their actual polynomial and character parameters.

The ray decomposition is also proved. In `ProjectiveRays.lean`, the map

$$
(P,t)\longmapsto tP.\mathrm{rep}
$$

is shown to be a bijection from
`Projectivization K V × Kˣ` to `{x : V // x ≠ 0}`. Its injectivity follows by
taking projective classes and then cancelling scalar multiplication on the
nonzero representative. Its surjectivity follows from the quotient relation
between a vector and its chosen projective representative. The exported
equivalence is `projectiveRayEquiv`.

`sum_cone_weighted_eq_sum_projective` transports the finite sum along this
equivalence. It then uses the proved scalar invariance of the cone and weight
to obtain

$$
\sum_{F(x)=0}\xi_p(x)e_p(u\cdot x)
=\sum_{P\in Q(\mathbf F_p)}\xi_p(P)
  \sum_{t\in\mathbf F_p^\times}e_p(tu\cdot P).
$$

The zero vector is removed using `ξ_p(0) = 0`. No partition formula or
cardinality formula for the quadric is supplied as a premise.

`stdAddChar_units_sum` evaluates the inner sum as `p-1` when its frequency is
zero and as `-1` otherwise. Its proof uses finite-field additive-character
orthogonality and removes the zero scalar; the primitivity of the standard
character and the cardinality of `ZMod p` are mathlib theorems. Finally,
`weighted_ray_sum` rearranges the two parts as `p*a_u - a`.

The resulting theorem `fourierSum_ray_identity` therefore proves (4.5) for
the actual Fourier and projective sums. It holds for every reduced frequency
because `a_0` has been defined. `fourierSum_zero` substitutes zero and gives
`(p-1)*a`; `integralFourierSum_of_dvd` gives the same value for every integral
frequency whose coordinates are all divisible by `p`. The two integral
wrappers account for both clauses of the displayed source identity.

## Hypotheses for the weight properties and exact identities

The Lean theorems are stronger statements in the sense that they require
fewer hypotheses for these exact identities. The differences do not restrict
the source's range of application.

| Manuscript hypothesis | Requirement for the checked algebraic clauses |
| --- | --- |
| `n ≥ 2` | `0 < n` suffices; the source implies it |
| `G` is an integral form of degree `n` | Integral homogeneity is accepted directly and preserved under reduction; a homogeneous reduced polynomial is also accepted directly |
| `ψ` is nonprincipal and `ψ^n` is principal | Only `ψ ^ n = 1` is required; the zero-extension convention is retained for principal characters |
| `A` is symmetric and nonsingular, with nonsquare determinant | No such conditions are needed for the identity `F(tx)=t²F(x)` or the ray partition |
| `p ∤ N_G`, in particular an odd prime of good reduction | Primality alone is needed for these clauses |
| Smoothness of `F=G=0` and the exceptional polynomial `D_p` | Neither enters the exact identity or the three weight properties |
| `p ∤ u` in the first clause of (4.5) | The formula holds for every frequency with `a_0=a`; the source's nonzero case follows immediately |

Positive degree is used to remove the origin. The stronger geometric and
nonprincipality assumptions remain essential inputs to the later estimates;
their absence here makes no claim about the validity of those estimates
without them. The zero polynomial is allowed by `IsHomogeneous n`, which also
handles a polynomial whose reduction becomes zero; this does not weaken any
conclusion in the reviewed scope.

## Modules completing the estimate

The completion adds the following seven modules. Each concerns either
literal geometric and arithmetic objects or an explicit elementary helper
subsequently applied to those objects.

| Module | Role |
| --- | --- |
| [PlaneRestriction.lean](../../QuaternaryQuadraticForms/PlaneRestriction.lean) | Nonvanishing of the quadratic form on the actual hyperplane and its ternary coordinate polynomial |
| [PolynomialGridCount.lean](../../QuaternaryQuadraticForms/PolynomialGridCount.lean) | Specialization of mathlib's proved Schwartz–Zippel theorem to a ternary polynomial of degree at most two |
| [PlaneSectionCardinality.lean](../../QuaternaryQuadraticForms/PlaneSectionCardinality.lean) | Exact affine/projective ray count, exceptional-section cardinality, and the norm of the actual section trace |
| [FourierBoundConstants.lean](../../QuaternaryQuadraticForms/FourierBoundConstants.lean) | The three elementary constant comparisons and the real-power identity |
| [FourierEstimates.lean](../../QuaternaryQuadraticForms/FourierEstimates.lean) | Generic, nonzero exceptional, and zero-frequency estimates for `fourierSum` |
| [FourierBound.lean](../../QuaternaryQuadraticForms/FourierBound.lean) | The indicator bound and all clauses for the literal integral data and modulus `N_G` |
| [FourierTheorem.lean](../../QuaternaryQuadraticForms/FourierTheorem.lean) | The uniformly bounded exceptional polynomial chosen before the character and frequency |

The existing `katz_quadric_bound_prime_field` supplies Lemma 2.7 for the
global projective trace. The existing `plane_section_bound_prime_field`
supplies Lemma 4.3 for a transverse section, including the internally
constructed parametrization of Lemma 4.2. Their correspondence is reviewed
in [katz_quadric.md](katz_quadric.md) and [plane_section.md](plane_section.md).
The construction of `D_p` is the proved Lemma 4.1(ii), reviewed in
[bad_reduction.md](bad_reduction.md).

## The exceptional-section count

The manuscript counts lines through a rational point of the plane outside
the quadric. The implementation proves the same required bound by a different
internal argument: a nonzero ternary quadratic restriction, the proved
Schwartz–Zippel estimate, and the exact decomposition into projective rays.
It does not assert that the manuscript's particular line-count proof has
been formalized.

Let `u ≠ 0`, and let `V = planeSubspace u` be the actual kernel of the
functional `x ↦ u · x`. Its dimension is three. The matrix is symmetric and
nonsingular, and two is nonzero in the field. If the quadratic value vanished
at every vector of `V`, polarization would give

$$
x^{\mathsf T}Ay=0\qquad(x,y\in V).
$$

Thus `V` would be contained in its orthogonal complement for the
nondegenerate matrix bilinear form. That complement has dimension one,
contradicting the dimension of `V`. The theorem
`plane_exists_nonzero_quadratic_value` proves this over any field with two
nonzero. It requires no nonvanishing of the dual quadratic and therefore
also covers tangent planes.

`planeCoordinateEquiv` supplies a linear equivalence from `K³` to `V`.
`planeRestrictionPolynomial` substitutes those linear coordinates into
the actual matrix quadratic polynomial. Its evaluation is proved to be the
original quadratic value on the corresponding vector; its homogeneity and
total-degree bound are also proved. The nonzero value just obtained proves
that this polynomial is nonzero. This implication uses an actual witness
and does not identify formal polynomials from their functions on a finite
field.

For `K = ZMod p`, `ternary_polynomial_zero_card_le` applies
`MvPolynomial.schwartz_zippel_totalDegree`, a proved theorem in the pinned
mathlib file `Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean`. Taking the
finite coordinate set to be the entire field gives at most `2p²` affine
zeros. An explicit equivalence of the two zero sets transports this bound
to the vectors satisfying the actual equations `F(x) = u · x = 0`.

Independently, `planeSection_affine_card_eq` uses the already proved ray
equivalence and the exact cardinality `p-1` of the field units to prove

$$
\#\{x\in\mathbf F_p^4:F(x)=u\cdot x=0\}
  =1+(p-1)M,
\qquad
M=\#\{P\in Q(\mathbf F_p):u\cdot P=0\}.
$$

The one counts the origin. Consequently `1+(p-1)M ≤ 2p²`.
Here `p` is an odd prime, so `p ≥ 3`. If `M ≥ 2p+3`, then
`1+(p-1)M ≥ 2p²+p-2 > 2p²`, a contradiction. This proves
`planeSection_card_le`, namely `M ≤ 2p+2`, with no smoothness or
transversality assumption on the plane section.

Finally `projectiveSectionTrace_norm_le` applies the triangle inequality
and the proved character bound to the literal sum over these points:

$$
|a_u|\le M\le 2p+2.
$$

This bound even allows arbitrary `G` and arbitrary multiplicative character;
the homogeneity, nonprincipality and geometric assumptions enter elsewhere
in the Fourier estimate. The exceptional-section proof adds no external
premise: the Schwartz–Zippel theorem and all linear algebra used here are
proved library results.

## The three frequency estimates and exact constants

`fourierSum_norm_le_section_and_trace` applies the triangle inequality to
the literal ray identity, obtaining

$$
|C_p(u)|\le p|a_u|+|a|.
$$

The norm of the complex natural-number scalar is exactly the corresponding
real number. `fourierSum_zero_norm` separately proves the exact formula
`‖C_p(0)‖ = (p-1)‖a‖`, using `p ≥ 1` to remove the absolute value from
the factor `p-1`. Thus no additional term is introduced in the zero case.

Write `B_n = 2n²-4n+4`. The geometric estimates are applied to the actual
polynomials, traces, matrix, and gradients as follows.

| Frequency case | Inputs and intermediate estimate | Final branch bound |
| --- | --- | --- |
| `D_p(u) ≠ 0` | Lemma 4.1(ii) supplies `F*(u) ≠ 0` and geometric rank three. Lemma 4.3 gives `\|a_u\| ≤ (2n-1)√p+1`; Lemma 2.7 gives `\|a\| ≤ B_n p`. Hence `\|C_p(u)\| ≤ (2n-1)p√p+(2n²-4n+5)p`. | `fourierSum_generic_bound`: `\|C_p(u)\| ≤ 2n²p√p` |
| Nonzero reduced `u`, including `D_p(u)=0` | The proved exceptional-section estimate gives `\|a_u\| ≤ 2p+2`, while Lemma 2.7 gives the same global bound. Hence `\|C_p(u)\| ≤ 2p²+(2n²-4n+6)p`. | `fourierSum_nonzero_bound`: `\|C_p(u)\| ≤ 2n²p²` |
| Zero reduced `u` | The exact zero-frequency identity and Lemma 2.7 give `\|C_p(u)\| ≤ (p-1)B_n p`. | `fourierSum_zero_bound`: `\|C_p(u)\| ≤ 2n²p²` |

The numerical comparisons in `FourierBoundConstants.lean` use only `n ≥ 2`
and `p ≥ 1`. In the generic case, `p ≤ p√p` gives coefficient
`2n²-2n+4 ≤ 2n²`. In the nonzero exceptional case, `p ≤ p²` gives
`2n²-4n+8 ≤ 2n²`. In the zero case, the nonnegative coefficient
`B_n ≤ 2n²` and `p-1 ≤ p` give the displayed bound. These numerical
lemmas are applied to estimates for the literal Fourier sum; they do not
replace the character-sum or geometric claims.

`rpow_three_halves_eq_mul_sqrt` proves
`p ^ (3 / 2 : ℝ) = p * Real.sqrt p` for every nonnegative real `p`.
The exponent in the final theorem is therefore the manuscript's real
exponent `3/2`, not integer division.

## The indicator, integral data, and literal modulus

`fourierSum_bound_prime_field` accepts any polynomial `D` vanishing at zero
and satisfying the outside-zero geometric conclusions of Lemma 4.1(ii).
It first separates the zero frequency, then separates `D(u)=0` from
`D(u)≠0`. At zero frequency, `D(0)=0` selects the exceptional indicator.
In both exceptional cases the stronger bound `2n²p²` implies

$$
|C_p(u)|\le 2n^2\bigl(p^{3/2}+p^2\bigr),
$$

since the added term is nonnegative. In the generic case the indicator
vanishes and the bound is exactly `2n²p^(3/2)`. This proves the complete
pointwise inequality with its stated indicator.

For this conditional inequality, nonzeroness and the degree of `D` need
not be assumed. They are retained in the uniform theorem below by actually
obtaining `D` from Lemma 4.1(ii). The conditional theorem therefore applies
to every exceptional polynomial allowed by the source, including the one
fixed in the opening hypotheses of Lemma 4.4.

`fourier_bound` accepts the original integral symmetric nonsingular matrix,
an integral form `G` homogeneous of degree `n ≥ 2`, the literal
`SmoothCharacteristicZero A G` assumption, and

```lean
¬ p ∣ polynomialBadPrimeModulus A G
  (badReductionPrimes_finite_of_smooth A hn G hG hsmooth)
```

The modulus is the actual product of the radical of `N_F` and the distinct
bad-reduction primes. Its finiteness argument is supplied by the proved
Lemma 4.1(i). The theorem does not substitute an arbitrary finite set or
ask the caller for a new good-reduction assumption.

The proved equivalence `not_dvd_polynomialBadPrimeModulus_iff` supplies
`p ∤ N_F` and `GoodReductionAt p A G`. These imply an odd prime, a
nonsingular reduced matrix, and the actual rank-two condition for the
coefficient-extended polynomials over `AlgebraicClosure (ZMod p)`.
Symmetry is preserved by coefficient reduction. All hypotheses of the
Katz, plane-section and exceptional-count estimates are thus discharged
from the source assumptions.

The conclusion of `fourier_bound` contains all five required assertions:
the three weight properties, the inequality for every `u : Fin 4 → ℤ`,
and the exact zero-frequency identity. The exceptional indicator is
literally

```lean
if MvPolynomial.eval (reduceFrequency p u) D = 0 then 1 else 0
```

so its input is the integral frequency reduced modulo `p`. An integral
frequency divisible by `p` in all coordinates is handled by the zero
residue case; it need not be the zero integer vector. The pre-existing
`integralFourierSum_of_dvd` still gives the exact identity for every such
frequency.

No condition `p ∤ n` is added anywhere. The degree conditions remain
homogeneity and `n ≥ 2`; the character condition is exactly `ψ ^ n = 1`.
Geometric hypotheses use the actual formal derivatives and ranks, also
when the characteristic divides the degree. No inverse of the degree is
introduced in these deductions. Nonsquareness of `det A`, a standing
assumption elsewhere in the manuscript, is unnecessary here; its omission
broadens the theorem without excluding any source instance.

## Uniformity and the order of quantifiers

The final export is `uniform_polynomial_fourier_bound`. For each fixed
integral `A` and `n`, it has the order

$$
\exists E\ge1\quad
\forall G\text{ satisfying the source assumptions}\quad
\forall p\nmid N_G\quad
\exists D_p\quad
\forall\psi\text{ with }\psi\ne1,\ \psi^n=1\quad
\forall u\in\mathbf Z^4.
$$

The theorem first invokes `exceptional_plane_polynomial A hA hdet n hn`.
It chooses `E` before the form and prime, and chooses `D_p` before the
character or frequency. Its conclusion retains `D_p ≠ 0`,
`D_p.totalDegree ≤ E`, `D_p(0)=0`, and the actual dual-form and geometric
rank-three properties outside its zero set. The same `D_p` then works
for every allowed character and every integral frequency. Thus neither
the degree bound nor the exceptional set acquires character dependence.

The construction does not assume that a transverse normal is rational
over the prime field. That issue was resolved in Lemma 4.1(ii) using a
geometric witness over the algebraic closure and descent of polynomial
nonvanishing. Nor does this theorem require a prime-field point outside
the zero set of `D_p`; its assertion is the conditional bound at every
frequency, exactly as in the source.

## Inspected axiom dependencies and conclusion

The actual `#check` types and `#print axioms` outputs for all 23 new
theorem exports were inspected after the final uniform wrapper compiled.
Every export uses only the standard foundations `propext`,
`Classical.choice`, and `Quot.sound`, together with the applicable entries
in this table. The table lists observed dependencies, rather than inferring
them from module imports.

| Export or group | Additional registered premises observed |
| --- | --- |
| Quadratic restriction, polynomial-grid count, affine and projective section counts, section-trace norm, numerical comparisons, ray-norm inequality, and exact zero-frequency norm | None |
| `fourierSum_generic_bound`, `fourierSum_bound_prime_field` | `Trusted.katz_surface_spectral_data`, `Trusted.weil_simple_roots` |
| `fourierSum_zero_bound`, `fourierSum_nonzero_bound` | `Trusted.katz_surface_spectral_data` |
| `fourier_bound` | `Trusted.katz_surface_spectral_data`, `Trusted.lang_homogeneous_resultants`, `Trusted.weil_simple_roots` |
| `uniform_polynomial_fourier_bound` | `Trusted.bertini_homogeneous_tangent`, `Trusted.katz_surface_spectral_data`, `Trusted.lang_homogeneous_resultants`, `Trusted.weil_simple_roots` |

The integral theorem includes Lang through the finite bad-prime set in
the literal modulus. The uniform theorem additionally uses the already
registered Bertini input through the construction of `D_p`. The exact
literature boundaries remain those reviewed in
[katz_input.md](katz_input.md), [weil_input.md](weil_input.md),
[elimination_input.md](elimination_input.md), and
[bertini_input.md](bertini_input.md). This completion adds no literature
premise and does not change any of their statements. In particular,
Schwartz–Zippel is used as a proved mathlib theorem, not as a new axiom.

Every source clause is now represented by an export about the actual
weight, Fourier sum, geometric rank conditions and exceptional polynomial.
The seven new modules, including `FourierTheorem.lean`, compiled under the
pinned Lean/mathlib environment with `warningAsError=true` and
`autoImplicit=false`. The inspected final types have the required
hypotheses and quantifier order, and this source review finds no omitted
clause or strengthened assumption.

This review supports complete classification of Lemma 4.4 once the full
repository verification gates pass. The live ledger, verification report
and execution checkpoint record that result, the input hashes, and the
exact checked commit/run evidence. A complete local lemma remains distinct
from certification of the whole manuscript.
