# Initial execution checkpoint

## Numbered-result status

Complete: **0**. Partial: **0**. Active numbered targets: **0**.
Pending: **42**. All 33 auxiliary/supplementary groups remain Pending.

The initial checkpoint records the complete numbered-result inventory and the
reviewed manuscript dependencies. It also proves one supporting identity:

[QuaternaryQuadraticForms.weighted_ray_sum](QuaternaryQuadraticForms/RayAlgebra.lean).

For a finite set of indices, a weight in a commutative ring, a predicate on the
indices, and a ring element p, this theorem combines the two ray contributions
p-1 and -1 into p times the weighted sum over the predicate minus the full
weighted sum. Its scope is the final finite algebra in (4.5). The finite-field
and projective interpretation remains to be formalized.

## Local execution

The local run passed the frozen-source and dependency checks, the complete
project build, and the inspection of the actual theorem type and its axioms.
The declaration is a theorem, with only the logical foundations
propext, Classical.choice, and Quot.sound. It has no external literature premise.

- Lean: official 4.24.0.
- mathlib: f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- Frozen manuscript: d4f42a201ae4af89b6884606d94480429a26cfa57332dca6a1547622a3acff33.
- Helper source: 7804a24cc6beb1de1a56d9f7ce305f128bcfae4fca376caef10cd0d853214480.
- [Actual verification report](certification/verification_report.json).

## GitHub execution

The same verifier passed in GitHub Actions on 13 November 2026
(America/Chicago), at the exact proof commit
[9e11229de99522eb324970953e91b38af275fddf](https://github.com/nicolasrobles/quaternary-quadratic-forms/tree/9e11229de99522eb324970953e91b38af275fddf).

- [Successful run 43545694187, attempt 1](https://github.com/nicolasrobles/quaternary-quadratic-forms/actions/runs/43545694187).
- Verification job: 132296365707.
- Artifact: 14093338686.
- [Preserved report](certification/ci/run_43545694187_attempt_1.json).
- [Preserved original artifact ZIP](certification/ci/run_43545694187_attempt_1.zip).
- ZIP SHA-256: 6e96f1d27c1aa312e2555e4a2f8ddf4e9d6a46b198a770b6f7e8972ec6fc2409.

The downloaded artifact was inspected. Its source, dependency, metadata, and
proof-file hashes all match the files at the checked checkpoint. It records
one kernel-checked supporting theorem and 42 Pending numbered results.
The later commit preserving this evidence changes documentation and records
only; the checked Lean source remains the commit linked above.

## Next target

Define the literal finite-field sums, prove invariance under projective
rescaling, evaluate the additive-character sum on each nonzero ray, and
complete (4.5). Then develop the polynomial power-sum argument for Lemma 5.9.
No internal result will be introduced as an assumed source input.
