# Lemma 3.6 recovery checkpoint

This branch now preserves the complete strictly checked source theorem for Lemma 3.6, together with all supporting proofs: 39 public theorem exports in 12 modules. The final source theorem has the exact gcd-filtered positive-modulus sum, arbitrary real cutoff X≥1, actual mixed and constrained sums, integral divisibility indicator, and a positive constant chosen before N, the local functions, q=q1*q2, u, and X.

All 12 modules passed strict compilation under pinned Lean 4.24.0; the final target build passed 3158 jobs. The combined actual type and axiom inspection exited successfully for all 39 exports. Every export uses only Classical.choice, Quot.sound, and propext; no literature premise is added. The complete source theorem is source_generic_modulus_bound in GenericModulusTheorem.lean.

These .lean.txt files preserve the exact Lean source bytes. checkpoint.json gives their restore paths, hashes, byte counts, public exports, and the unified inspection log. The previous inspection logs are retained from earlier recovery checkpoints.

Certification integration, the full aggregate verifier and baseline comparison, and exact-commit GitHub CI remain outstanding. The certified main branch still has the completed Lemma 3.5 milestone, where Lemma 3.6 is Pending. This recovery checkpoint does not claim that those remaining verification gates have passed.
