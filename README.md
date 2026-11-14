# Character sums over zeros of quaternary quadratic forms

Source-relative Lean verification of the paper by Hemjyoti Nath, Nicolas Robles,
and Alexandru Zaharescu.

The mathematical source is the audited **v35**, copied without content changes as
[quadratic_character_sums_github.tex](manuscript/quadratic_character_sums_github.tex).
The associated [34-page PDF](manuscript/quadratic_character_sums_github.pdf) is
included. The source SHA-256 is

    d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33

## Current status

**Complete: 0 · Partial: 2 · Active: 0 · Pending: 40** — 42 numbered results.

Lemma 4.4 is **Partial**: its three weight properties, exact zero-frequency
formula, and intermediate ray identity (4.5) are checked; its pointwise Fourier
bound remains pending. Lemma 5.9 is now **Partial**: integrality and divisibility
of the actual quadratic projective trace are checked locally and in
[GitHub Actions](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43550688913), while the bound
`|a_p(G)| ≤ 4p` remains pending.

The ledger registers 40 checked exports across nine proof modules. All 33
separate auxiliary/supplementary groups remain Pending. This repository does
not yet provide a certificate for the whole paper. The execution checkpoint
records the exact scope and evidence for each verification run.

- [Certification inventory, with links to checked exports](INVENTORY.md)
- [Dependency graphs and the proof structure](DEPENDENCIES.md)
- [Trusted literature inputs and excluded comparison claims](TRUSTED_INPUTS.md)
- [Live proof ledger](certification/status.json)
- [Actual Lean types and axiom dependencies](certification/verification_report.json)
- [Correspondence review for the Fourier ray identity](certification/correspondence/fourier_rays.md)
- [Correspondence review for quadratic-trace divisibility](certification/correspondence/quadratic_trace.md)
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

No external literature premise has been introduced into Lean at this checkpoint.

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
      Mathlib.NumberTheory.LegendreSymbol.Basic
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

The next branch concerns the finite-field estimates: register the precise
Weil and Katz input interfaces and prove the manuscript's specializations.
Corollary 2.6, the projective-line estimate, is a practical first target.
The Katz specialization in Lemma 2.7 and the remaining geometric clauses of
Lemma 4.4 require their own hypothesis checks and deductions. Once the relevant
trace bound is available, it also supplies the remaining size clause of
Lemma 5.9.
