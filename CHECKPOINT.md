# Fourier-ray execution checkpoint

## Numbered-result status

Complete: **0**. Partial: **1**. Active numbered targets: **0**.
Pending: **41**. All 33 auxiliary/supplementary groups remain Pending.

The partial numbered result is **Lemma 4.4**. The checked clauses are the
three weight properties (3.1) and the exact zero-frequency formula in (4.4).
The complete intermediate ray identity (4.5) is also proved. The pointwise
bound involving the exceptional polynomial remains pending.

## Mathematical scope

The formalization now uses the actual four-dimensional prime-field vector
space, matrix quadratic form, homogeneous multivariate polynomial,
multiplicative character extended by zero, standard additive character, and
projective quotient. It proves representative independence of the quadric
condition, the hyperplane condition, and the character weight.

The nonzero vectors are parametrized bijectively by projective points and
nonzero scalars. The additive-character sum on each ray is evaluated, and the
result is assembled as C_p(u) = p*a_u - a, including a_0 = a. Integral matrix
and polynomial coefficients and integral frequencies are reduced explicitly;
p divides u exactly when it divides every coordinate.

- [Main Fourier identities](QuaternaryQuadraticForms/FourierRays.lean).
- [Precise statement correspondence](certification/correspondence/fourier_rays.md).
- [Inventory of the 19 checked exports](INVENTORY.md).
- [Updated full dependency graph PNG](docs/dependency_graph.png).
- [Updated overview PNG](docs/dependency_overview.png).

These identities do not need the geometric hypotheses required for the
later estimates. Those estimates and their manuscript-specific deductions
have not been introduced as assumptions.

## Local execution

The complete verifier passed on 14 November 2026 at 02:34 UTC. It checked the
frozen manuscript and PDF, all 42 numbered statement identities, the dependency
ledger, pinned library checkouts, all five local proof modules, and the 19
registered theorem declarations with their actual types and axiom dependencies.
All modules were checked with warningAsError=true and autoImplicit=false.

Every inspected theorem uses only propext, Classical.choice, and Quot.sound.
There are zero registered external Lean premises. No placeholder, native
evaluation, or unchecked local axiom was introduced.

- Lean: official 4.24.0.
- mathlib: f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- Frozen manuscript: d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33.
- [Local verification report, including input hashes](certification/verification_report.json).

The verifier now also binds the correspondence review to the report by its
SHA-256 and requires each Partial item to list both completed and remaining
clauses. The graph renderer reads the live status ledger, so the PNG, SVG,
PDF and DOT views display the same status as the inventory.

## GitHub execution

Publication of this checkpoint triggers the same verification workflow. Its
run and preserved artifact will be recorded here after execution succeeds.
The preceding successful initial checkpoint remains preserved in
[run_43545694187_attempt_1.json](certification/ci/run_43545694187_attempt_1.json)
and its associated ZIP. That earlier run checked the initial algebra helper;
it is not evidence for the new finite-field identities.

## Next target

Proceed to the polynomial power-sum argument proving the divisibility clause
of Lemma 5.9. Its size bound is a separate obligation. Completing Lemma 4.4
also requires the precise literature interfaces, geometric specializations,
plane-section bound, and exceptional-frequency count listed in the
correspondence review. Preserve the checked ray identity as a completed input.
