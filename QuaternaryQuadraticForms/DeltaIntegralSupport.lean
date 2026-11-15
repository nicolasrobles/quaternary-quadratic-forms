import QuaternaryQuadraticForms.AnalyticDefinitions
import QuaternaryQuadraticForms.DeltaSymbolTheorem
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The actual integral and its derivative above the kernel cutoff

Only the already certified kernel support is used. Compactness and the
quadratic-form bound that supply a common `M` are separate internal proofs.
The strict margin also makes the integral locally zero at every scale in
the final closed cutoff range, which proves its actual derivative is zero.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory Filter
open scoped Topology

/-- A zero weight has zero actual oscillatory integral at every parameter. -/
theorem deltaIntegral_zero_weight (F : RealVector4 → ℝ) (r : ℝ)
    (v : RealVector4) : deltaIntegral F 0 r v = 0 := by
  simp [deltaIntegral]

/-- The kernel support cuts off the actual integral once the scale exceeds
the common bound on the quadratic value on the weight's support. -/
theorem deltaIntegral_eq_zero_of_support_bound
    (F : RealVector4 → ℝ) (w : RealVector4 → ℂ) (M : ℝ)
    (hM : ∀ x ∈ tsupport w, |F x| ≤ M)
    (r : ℝ) (hr : max 1 (2 * M) < r) (v : RealVector4) :
    deltaIntegral F w r v = 0 := by
  unfold deltaIntegral
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hw : w x = 0
  · simp [hw]
  · have hx : x ∈ tsupport w := subset_tsupport w hw
    have hbound : max 1 (2 * |F x|) < r :=
      (max_le_max_left 1 (mul_le_mul_of_nonneg_left (hM x hx) (by norm_num))).trans_lt hr
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1)
      ((le_max_left 1 (2 * M)).trans_lt hr)
    rw [heathBrownDeltaKernel_properties.2.2 r (F x) hrpos hbound]
    simp

/-- The actual parameter function is locally constant zero above the cutoff. -/
theorem deltaIntegral_eventually_zero
    (F : RealVector4 → ℝ) (w : RealVector4 → ℂ) (M : ℝ)
    (hM : ∀ x ∈ tsupport w, |F x| ≤ M)
    (r : ℝ) (hr : max 1 (2 * M) < r) (v : RealVector4) :
    (fun s : ℝ => deltaIntegral F w s v) =ᶠ[𝓝 r] fun _ => 0 := by
  filter_upwards [eventually_gt_nhds hr] with s hs
  exact deltaIntegral_eq_zero_of_support_bound F w M hM s hs v

/-- The derivative is with the original frequency fixed. -/
theorem hasDerivAt_deltaIntegral_zero
    (F : RealVector4 → ℝ) (w : RealVector4 → ℂ) (M : ℝ)
    (hM : ∀ x ∈ tsupport w, |F x| ≤ M)
    (r : ℝ) (hr : max 1 (2 * M) < r) (v : RealVector4) :
    HasDerivAt (fun s : ℝ => deltaIntegral F w s v) 0 r := by
  exact (hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq
    (deltaIntegral_eventually_zero F w M hM r hr v)

/-- In particular the actual derivative vanishes above the cutoff. -/
theorem deriv_deltaIntegral_eq_zero_of_support_bound
    (F : RealVector4 → ℝ) (w : RealVector4 → ℂ) (M : ℝ)
    (hM : ∀ x ∈ tsupport w, |F x| ≤ M)
    (r : ℝ) (hr : max 1 (2 * M) < r) (v : RealVector4) :
    deriv (fun s : ℝ => deltaIntegral F w s v) r = 0 :=
  (hasDerivAt_deltaIntegral_zero F w M hM r hr v).deriv

/-- A single closed cutoff works for every weight sharing the bound `M`.
The extra unit gives the strict neighborhood needed for derivatives. -/
theorem deltaIntegral_uniform_cutoff (F : RealVector4 → ℝ) (M : ℝ) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ w : RealVector4 → ℂ,
      (∀ x ∈ tsupport w, |F x| ≤ M) → ∀ r : ℝ, r₀ ≤ r →
        ∀ v : RealVector4, deltaIntegral F w r v = 0 ∧
          HasDerivAt (fun s : ℝ => deltaIntegral F w s v) 0 r := by
  refine ⟨max 1 (2 * M) + 1, ?_, ?_⟩
  · linarith [le_max_left (1 : ℝ) (2 * M)]
  · intro w hw r hr v
    have hstrict : max 1 (2 * M) < r := by linarith
    exact ⟨deltaIntegral_eq_zero_of_support_bound F w M hw r hstrict v,
      hasDerivAt_deltaIntegral_zero F w M hw r hstrict v⟩

end QuaternaryQuadraticForms
