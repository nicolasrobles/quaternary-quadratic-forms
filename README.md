# Character sums over zeros of quaternary quadratic forms

Source-relative Lean verification of the paper by Hemjyoti Nath, Nicolas Robles,
and Alexandru Zaharescu.

The mathematical source is the audited **v35**, copied without content changes as
[quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).
The associated [34-page PDF](manuscript/quadratic_character_sums_github.pdf) is
included. The source SHA-256 is

    d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33

## Current status

**Complete: 2 · Partial: 2 · Active: 0 · Pending: 38** — 42 numbered results.

**Lemma 2.5 and Corollary 2.6 are Certified relative to the accepted literature
inputs.** Lemma 2.5 is matched to the exact cited univariate Weil estimate.
Corollary 2.6 is proved for the actual projective-line character sum, including
the chart decomposition, polynomial dehomogenization, degree calculation,
distinct-root condition, and contribution at infinity.

Lemma 4.4 remains **Partial**: its three weight properties, exact zero-frequency
formula, and intermediate ray identity (4.5) are checked; its pointwise Fourier
bound remains pending. Lemma 5.9 remains **Partial**: integrality and divisibility
of the actual quadratic projective trace are checked; the bound
`|a_p(G)| ≤ 4p` remains pending.

The ledger registers 68 checked theorem exports and one separate trusted
literature premise across 16 Lean modules. All 33 auxiliary/supplementary groups
remain Pending. This repository does not yet provide a certificate for the
whole paper. The execution checkpoint records the exact scope and evidence
for each verification run.

This checkpoint passed locally and in [GitHub Actions](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43551946447)
at [proof commit 450ff67](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/450ff678b56b0a32a76b848278b53ba697958939).
The downloaded CI report and original artifact are preserved in the repository.

- [Certification inventory, with links to checked exports](INVENTORY.md)
- [Dependency graphs and the proof structure](DEPENDENCIES.md)
- [Trusted literature inputs and excluded comparison claims](TRUSTED_INPUTS.md)
- [Live proof ledger](certification/status.json)
- [Actual Lean types and axiom dependencies](certification/verification_report.json)
- [Correspondence review for the Fourier ray identity](certification/correspondence/fourier_rays.md)
- [Correspondence review for quadratic-trace divisibility](certification/correspondence/quadratic_trace.md)
- [Correspondence review for the Weil input](certification/correspondence/weil_input.md)
- [Correspondence review for the projective-line bound](certification/correspondence/projective_weil.md)
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

One external premise is registered: the simple-root univariate Weil estimate
from [K, equation (1.2)], specialized to the prime field. Its exact type,
source correspondence, and type hash are inspected separately from proved
exports. The projective-line deductions use this input and the official library;
they are not included among the trusted assumptions.

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
`D_p`, including its generic and exceptional frequency cases. The
[correspondence record](certification/correspondence/fourier_rays.md) separates
the completed clauses from those obligations.

## Quadratic-trace divisibility

For an odd prime and a quadratic homogeneous `G`, the new branch proves

$$a_p(G)\in\mathbb Z,\qquad p\mid a_p(G).$$

The trace is first constructed as an integer sum of quadratic-character
values, then its complex cast is identified with the projective trace already
used in the Fourier identities. Euler's criterion and mathlib's polynomial-sum
vanishing theorem show that the affine trace is zero modulo `p`. The checked
identity `C_p(0) = (p-1)a_p(G)` then gives projective divisibility.

This argument needs neither nonsingularity nor smoothness. Those hypotheses
belong to the separate size estimate in Lemma 5.9, which is still pending.
The [correspondence review](certification/correspondence/quadratic_trace.md)
records the exact integer and complex statements and their specialization to
the manuscript.

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
      Mathlib.Algebra.Polynomial.Homogenize \
      Mathlib.Data.Fin.VecNotation \
      Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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

The projective-line estimate is now available for the plane-section argument.
The next deductions are the conic parametrization in Lemma 4.2 and its use in
the plane-section estimate of Lemma 4.3, with the geometric hypotheses checked
on the actual forms and projective sets.

The Katz specialization in Lemma 2.7 is a separate remaining branch. Its
precise literature interface and manuscript-specific geometric deductions
are still pending. It supplies the global trace bound needed for the remaining
clauses of Lemmas 4.4 and 5.9.
