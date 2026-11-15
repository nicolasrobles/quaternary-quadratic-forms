import QuaternaryQuadraticForms.DeltaSymbolDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Registered literature input: Heath--Brown's fixed delta construction

This is the construction-level external input registered as EXT.HB_DELTA,
not a proved manuscript result. The actual bump, sampling sum and kernel
are defined in DeltaSymbolDefinitions. The source is Heath--Brown,
Theorem 1 and Sections 2--3, especially (3.1)--(3.3) and the unnormalized
orthogonality calculation. See certification/correspondence/delta_symbol.md.

The input contains the raw sampling error and unnormalized delta identity.
Positivity and uniform rapid approximation of Q/S(Q) for Q >= 3, the
normalized identity, and finite support of the outer sum are internal
proofs. No positive normalizer at Q=2 is asserted. The scoped smooth
order below is infinity, not the library's analytic top order.
-/

noncomputable section

open scoped BigOperators ContDiff

axiom QuaternaryQuadraticForms.Trusted.heathBrown_delta_data :
  Continuous QuaternaryQuadraticForms.heathBrownBump ∧
  (∀ t : ℝ, 0 ≤ QuaternaryQuadraticForms.heathBrownBump t) ∧
  (∀ t : ℝ, 1 / 2 < t → t < 1 → 0 < QuaternaryQuadraticForms.heathBrownBump t) ∧
  (∀ t : ℝ, ¬(1 / 2 < t ∧ t < 1) → QuaternaryQuadraticForms.heathBrownBump t = 0) ∧
  ContDiffOn ℝ ∞ QuaternaryQuadraticForms.heathBrownDeltaKernel {z : ℝ × ℝ | 0 < z.1} ∧
  (∃ B : ℝ, 0 < B ∧ ∀ x y : ℝ, 0 < x →
    |QuaternaryQuadraticForms.heathBrownDeltaKernel (x, y)| ≤ B / x) ∧
  (∀ x y : ℝ, 0 < x → max 1 (2 * |y|) < x →
    QuaternaryQuadraticForms.heathBrownDeltaKernel (x, y) = 0) ∧
  (∀ Q : ℝ, 1 < Q → ∀ n : ℤ,
    (∑' c : ℕ+, QuaternaryQuadraticForms.deltaSymbolTerm
      QuaternaryQuadraticForms.heathBrownDeltaKernel Q n c) =
      ((Q * QuaternaryQuadraticForms.heathBrownSamplingSum Q : ℝ) : ℂ) *
        (if n = 0 then 1 else 0 : ℂ)) ∧
  (∀ m : ℕ, 2 ≤ m → ∃ A : ℝ, 0 < A ∧ ∀ Q : ℝ, 1 < Q →
    |QuaternaryQuadraticForms.heathBrownSamplingSum Q - Q| ≤ A * Q / Q ^ m)
