import QuaternaryQuadraticForms.AnalyticDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Internal frequency rescaling for the delta integral

The source oscillatory estimates use the frequency `u = r⁻¹ • v`.
This module checks its Euclidean norm and the resulting natural and real
powers of `r`. It also combines the value and fixed-frequency derivative
bounds. Every result is scalar algebra or a norm identity; no literature
premise is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The source frequency has exactly the manuscript's Euclidean scaling. -/
theorem deltaIntegral_rescaledFrequency_norm {r : ℝ} (hr : 0 < r)
    (v : RealVector4) : ‖r⁻¹ • v‖ = ‖v‖ / r := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    div_eq_mul_inv, mul_comm]

/-- Natural-order rapid decay after the substitution `u = r⁻¹ • v`.
Inverse natural powers also cover `j = 0` and `v = 0` without extra hypotheses. -/
theorem deltaIntegral_rapid_scale_identity {r : ℝ} (hr : 0 < r)
    (v : RealVector4) (j : ℕ) :
    r⁻¹ * ((r ^ j)⁻¹ * (‖r⁻¹ • v‖ ^ j)⁻¹) =
      r⁻¹ * (‖v‖ ^ j)⁻¹ := by
  congr 1
  rw [deltaIntegral_rescaledFrequency_norm hr, div_pow, inv_div,
    div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hr.ne'), one_mul]

/-- The four-dimensional Hessian estimate has the precise manuscript exponents.
The algebra holds for every real exponent, so the analytic restriction on
`ε` is needed only in the source estimate, not in this rescaling. -/
theorem deltaIntegral_epsilon_scale_identity {r : ℝ} (hr : 0 < r)
    {v : RealVector4} (hv : v ≠ 0) (ε : ℝ) :
    r⁻¹ * ((r⁻¹ * ‖r⁻¹ • v‖) ^ ε * r * ‖r⁻¹ • v‖⁻¹) =
      r ^ (1 - 2 * ε) * ‖v‖ ^ (-1 + ε) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hrpow : r ^ ε ≠ 0 := (Real.rpow_pos_of_pos hr ε).ne'
  have hscale : r ^ (1 - 2 * ε) = r / (r ^ ε) ^ 2 := by
    rw [Real.rpow_sub hr, Real.rpow_one,
      show (2 : ℝ) * ε = ε * (2 : ℝ) by ring,
      Real.rpow_mul hr.le, Real.rpow_two]
  have hnorm : ‖v‖ ^ (-1 + ε) = ‖v‖ ^ ε / ‖v‖ := by
    rw [show (-1 + ε : ℝ) = ε - 1 by ring,
      Real.rpow_sub_one hvpos.ne']
  rw [deltaIntegral_rescaledFrequency_norm hr, hscale, hnorm,
    Real.mul_rpow (inv_nonneg.mpr hr.le) (div_nonneg (norm_nonneg v) hr.le),
    Real.inv_rpow hr.le, Real.div_rpow (norm_nonneg v) hr.le]
  field_simp [hr.ne', hvpos.ne', hrpow]

/-- Multiplying the derivative estimate by `r` gives the same scale as
the value estimate, with the two constants added. -/
theorem deltaIntegral_value_derivative_scale_add {r : ℝ} (hr : r ≠ 0)
    (C D B : ℝ) :
    C / r * B + r * (D / r ^ 2 * B) = (C + D) * (r⁻¹ * B) := by
  field_simp [hr]

/-- Equal constants in the two source bounds produce a factor of two. -/
theorem deltaIntegral_value_derivative_scale_double {r : ℝ} (hr : r ≠ 0)
    (C B : ℝ) :
    C / r * B + r * (C / r ^ 2 * B) = 2 * C * (r⁻¹ * B) := by
  rw [deltaIntegral_value_derivative_scale_add hr]
  ring

/-- Combine independently obtained bounds for a value and its derivative.
The two source witness integrals need only share the numerical upper bound `B`. -/
theorem deltaIntegral_combine_value_derivative_bounds {r : ℝ} (hr : 0 < r)
    {C D B : ℝ} {I J : ℂ}
    (hI : ‖I‖ ≤ C / r * B) (hJ : ‖J‖ ≤ D / r ^ 2 * B) :
    ‖I‖ + r * ‖J‖ ≤ (C + D) * (r⁻¹ * B) := by
  calc
    ‖I‖ + r * ‖J‖ ≤ C / r * B + r * (D / r ^ 2 * B) :=
      add_le_add hI (mul_le_mul_of_nonneg_left hJ hr.le)
    _ = (C + D) * (r⁻¹ * B) :=
      deltaIntegral_value_derivative_scale_add hr.ne' C D B

end QuaternaryQuadraticForms
