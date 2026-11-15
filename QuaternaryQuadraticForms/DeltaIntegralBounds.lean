import QuaternaryQuadraticForms.AnalyticDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The simultaneous uniform conclusions for the actual delta integral

The scale set lets the source estimates on a bounded range be separated
from the internal extension above the actual kernel cutoff. The value
functional sigma is explicit; its identification with the actual surface
integral is a separate internal proof. Every constant precedes the weight.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- All four estimates, with actual fixed-frequency differentiability and
common constants over the entire indicated family. -/
structure DeltaIntegralBounds (F : RealVector4 → ℝ)
    (sigma : (RealVector4 → ℂ) → ℂ)
    (weights : Set (RealVector4 → ℂ)) (scales : Set ℝ) : Prop where
  differentiable : ∀ w ∈ weights, ∀ r ∈ scales, ∀ v : RealVector4,
    DifferentiableAt ℝ (fun t => deltaIntegral F w t v) r
  zero_error : ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ weights, ∀ r ∈ scales,
      ‖deltaIntegral F w r 0 - sigma w‖ ≤ C * r ^ j
  zero_derivative : ∃ C : ℝ, 0 < C ∧ ∀ w ∈ weights, ∀ r ∈ scales,
    ‖deriv (fun t => deltaIntegral F w t 0) r‖ ≤ C * r⁻¹
  rapid : ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ weights, ∀ r ∈ scales, ∀ v : RealVector4, v ≠ 0 →
      ‖deltaIntegral F w r v‖ ≤ C * r⁻¹ * ‖v‖⁻¹ ^ j
  decay : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ weights, ∀ r ∈ scales, ∀ v : RealVector4, v ≠ 0 →
      ‖deltaIntegral F w r v‖ + r * ‖deriv (fun t => deltaIntegral F w t v) r‖ ≤
        C * r ^ (1 - 2 * ε) * ‖v‖ ^ (-1 + ε)

end QuaternaryQuadraticForms

