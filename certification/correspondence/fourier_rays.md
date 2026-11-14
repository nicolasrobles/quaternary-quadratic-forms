# Source correspondence: the weight properties and Fourier ray identity

## Scope and source

This review covers the three properties of the polynomial character weight in
equation (3.1), the complete ray identity (4.5), and the exact zero-frequency
clause of Lemma 4.4. It supports a **Partial** classification for Lemma 4.4.
The bound involving the exceptional polynomial `D_p` is outside the checked
scope described here.

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

Equation (3.1) is an assumption on arbitrary functions in Section 3. The
formalized result verifies that assumption for the Section 4 specialization
`ξ_p(x) = ψ(G(x))`. It does not assert that an arbitrary function on the vector
space has those properties.

## The objects in the formal statements

The implementation is in
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

## Hypotheses and the direction of specialization

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

## Remaining obligations and status recommendation

Lemma 4.4 also asserts

$$
|C_p(u)|\le 2n^2\bigl(p^{3/2}+p^2\mathbf 1_{D_p(u)=0}\bigr).
$$

That bound, at source lines 1803–1805 and in the proof at lines 1823–1847, is
not established by these exports. Two of its local inputs are now proved:
`katz_quadric_bound` supplies Lemma 2.7 for the complete projective trace,
and `plane_section_bound` supplies Lemma 4.3 for the transverse section
trace, including the internally constructed parametrization of Lemma 4.2.
Their source correspondence and hypotheses are documented in
[katz_quadric.md](katz_quadric.md) and [plane_section.md](plane_section.md).
The remaining deductions for the full Fourier estimate include:

- Lemma 4.1 (`lem:exceptional`): construction of `D_p`, its degree bound,
  good-reduction conditions, and the required transversality consequence;
- the exceptional-section counting argument at lines 1833–1842, including
  nonvanishing of the restricted quadratic form and the bound `2p+2`;
- the specialization and arithmetic combination of these bounds with the
  proved ray identity, including the final constant `2n²`.

Exact cited literature inputs may be trusted under the project's policy once
their interfaces and locators are registered. The manuscript's own Lemmas
2.7, 4.1 and 4.3, and its geometric specializations and deductions, cannot be
introduced as replacement axioms. None of those literature interfaces or
internal estimates is needed as a premise of the present identities. The
proved Katz and plane-section bounds are available for the subsequent
estimate; their availability alone does not complete its remaining steps.

The recommended numbered-result status is consequently **Partial for Lemma
4.4**, covering all three weight properties and its exact zero-frequency
clause. Equation (4.5) is a completed supporting identity; it is not a separate
numbered theorem, and it does not make the entire lemma Certified.

The reviewed `FourierRays.lean` module, including the hyperplane
representative-independence theorem and the integral wrappers, compiled under
the pinned Lean/mathlib environment with `warningAsError=true` and
`autoImplicit=false`. This statement is limited to module compilation and
source correspondence. The repository's verifier and execution records supply
the exact export types, permitted axiom dependencies, source hashes, checked
commit, and project-wide build/CI result. Neither module compilation nor this
review is a certificate for the whole paper.
