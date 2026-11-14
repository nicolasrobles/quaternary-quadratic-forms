# Quadratic-trace divisibility checkpoint

## Numbered-result status

Complete: **0**. Partial: **2**. Active numbered targets: **0**.
Pending: **40**. All 33 auxiliary/supplementary groups remain Pending.

The new Partial result is **Lemma 5.9**. Its integrality and divisibility
clauses are proved for the actual projective quadratic-character trace.
The size bound |a_p(G)| ≤ 4p remains pending. Lemma 4.4 retains its checked
weight properties, ray identity and exact zero-frequency clause; its
pointwise estimate remains pending.

## Mathematical scope

The proof constructs integer-valued affine and projective sums of the
quadratic character and identifies their complex casts with the sums already
used in the Fourier identity. The matrix expression x^T A x is represented
by an explicitly defined homogeneous quadratic polynomial. Its evaluation
identity and degree bound are proved.

Euler's criterion and the polynomial zero-locus indicator turn the affine
sum modulo p into the sum of (1-F^(p-1))*G^(p/2). The proof checks the strict
degree threshold and applies the official mathlib polynomial-sum theorem.
This proves divisibility of the integer affine sum. The established ray
identity yields C=(p-1)*a over the integers; reducing this equality modulo p
proves divisibility of the projective trace.

The final export gives an explicit integer a whose complex cast is the
paper's trace and for which p divides a. It includes reduction of integral
matrix and form coefficients. The trace's independence of projective
representatives is proved under quadratic homogeneity.

- [Main trace statements](QuaternaryQuadraticForms/QuadraticTrace.lean).
- [Affine divisibility proof](QuaternaryQuadraticForms/AffineDivisibility.lean).
- [Statement correspondence](certification/correspondence/quadratic_trace.md).
- [Inventory with links to all checked exports](INVENTORY.md).
- [Full dependency graph PNG](docs/dependency_graph.png).
- [Overview PNG](docs/dependency_overview.png).

The divisibility result needs an odd prime and a homogeneous quadratic G.
It does not need the geometric hypotheses required for the pending size
estimate. No internal lemma or estimate has been introduced as an external
premise.

## Local execution

The full verifier passed on 13 November 2026 at 21:13 CST. It checked the frozen
manuscript and PDF, all 42 numbered statement identities, the dependency
ledger, pinned library checkouts, all nine local proof modules, and all 40
registered theorem declarations with their actual types and axiom dependencies.
The direct Lean checks use warningAsError=true and autoImplicit=false.

Every inspected theorem uses only propext, Classical.choice, and Quot.sound.
There are zero registered external Lean premises. Both correspondence
records are bound to the report by SHA-256. The live ledger records the
completed and remaining clauses of both Partial numbered results.

- Lean: official 4.24.0.
- mathlib: f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- Frozen manuscript: d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33.
- [Local verification report and input hashes](certification/verification_report.json).

## GitHub execution

The same verifier passed in GitHub Actions at the exact proof commit
[ee274f6752d5a28e875919349821518b297e3115](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/ee274f6752d5a28e875919349821518b297e3115).

- [Successful run 43550688913, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43550688913).
- Verification job: 132312192673.
- Artifact: 14095862449.
- [Preserved CI report](certification/ci/run_43550688913_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43550688913_attempt_1.zip).
- ZIP SHA-256: 182154b8c40d97d9f25aef44b4884d0575fd998c840ff477816fc6dd957f1ec1.
- Report SHA-256: 5857644248cb0e950e22ff317e8cc918b8cd3199de407af7e6b0f954f9375002.

The downloaded artifact was inspected. All 21 recorded input hashes match
the checked files, including both correspondence records. All 40 theorem
records match the locally inspected actual types and axiom dependencies.
The CI report records two Partial numbered results, 40 Pending numbered
results, and zero external Lean premises.

The later commit preserving this evidence changes documentation and records
only. The proof sources, checker, status ledger, and correspondence records
remain those of the checked proof commit linked above.

## Earlier checked checkpoints

The complete ray identity was checked at proof commit
[9c9840ed04c90a22af480eec1e1fe6eee168487b](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/9c9840ed04c90a22af480eec1e1fe6eee168487b),
with [successful run 43547207971](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43547207971).
Its [report](certification/ci/run_43547207971_attempt_1.json) and
[original artifact](certification/ci/run_43547207971_attempt_1.zip) remain preserved.
The initial algebra-only report is also preserved as
[run_43545694187_attempt_1.json](certification/ci/run_43545694187_attempt_1.json).

## Next target

Proceed to the finite-field estimate branch. First record the precise
univariate Weil input used in Lemma 2.5, then prove the manuscript's
projective-line Corollary 2.6, including the affine-chart decomposition and
the degree and simple-root conditions after dehomogenization. This provides
a concrete next estimate toward the plane-section argument.

The Katz interface and the geometric specialization in Lemma 2.7 are a
separate branch. They are needed for the remaining size clause of Lemma 5.9
and the global trace contribution to Lemma 4.4. Trusted published inputs may
be assumed at their exact scope; the manuscript's hypotheses and deductions
remain to be verified.
