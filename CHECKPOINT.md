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

The same verifier passed in GitHub Actions at the exact proof commit
[9c9840ed04c90a22af480eec1e1fe6eee168487b](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/9c9840ed04c90a22af480eec1e1fe6eee168487b).

- [Successful run 43547207971, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43547207971).
- Verification job: 132301195594.
- Artifact: 14094418614.
- [Preserved CI report](certification/ci/run_43547207971_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43547207971_attempt_1.zip).
- ZIP SHA-256: 067d30301e01e43e376c4b2da72f3ef0311a0dca5eb850694dc002702edaf6a7.
- Report SHA-256: 5b593601c51e33e8dd68a19f7af607c97688897cb860ab2e6212015a671afb7b.

The downloaded report was inspected. All 16 recorded input hashes match the
checked source, including the correspondence record, and all 19 theorem
records match the locally inspected types and axiom dependencies. The report
records one Partial numbered result, 41 Pending numbered results, and zero
external Lean premises. The later commit preserving this evidence changes
documentation and records only; the proof code, checker, and live status
remain those of the checked commit linked above.

The initial algebra-only checkpoint remains preserved separately in
[run_43545694187_attempt_1.json](certification/ci/run_43545694187_attempt_1.json)
and its associated ZIP.

## Next target

Proceed to the polynomial power-sum argument proving the divisibility clause
of Lemma 5.9. Its size bound is a separate obligation. Completing Lemma 4.4
also requires the precise literature interfaces, geometric specializations,
plane-section bound, and exceptional-frequency count listed in the
correspondence review. Preserve the checked ray identity as a completed input.

The pinned official mathlib already supplies the polynomial-grid vanishing
lemma MvPolynomial.sum_eval_eq_zero in Mathlib.FieldTheory.ChevalleyWarning.
The next implementation should specialize it to
(1 - F^(p-1)) * G^((p-1)/2), using the literal integer-valued quadratic
character, and then use the checked zero-frequency identity to pass from the
affine sum to the integer-valued projective trace. The trace must first be
constructed over the integers and compared with its complex cast; divisibility
is not asserted directly of an arbitrary complex-valued character sum.
