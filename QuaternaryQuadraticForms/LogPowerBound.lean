import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform powers of the logarithm

Every fixed nonnegative integral power of `1 + log X` is bounded by
an arbitrary positive real power of `X`, uniformly for `X ≥ 1`.
The constant is chosen before `X`; the proof uses the proved real
inequality `log X ≤ X^δ / δ` and handles exponent zero separately.
-/

namespace QuaternaryQuadraticForms

/-- A fixed power of `1 + log X` is absorbed by any prescribed positive
power of `X`, with one positive constant uniform for every `X ≥ 1`. -/
theorem one_add_log_pow_le_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (1 + Real.log X) ^ k ≤ C * X ^ ε := by
  by_cases hk : k = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro X hX
    simpa [hk] using Real.one_le_rpow hX hε.le
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  let δ : ℝ := ε / (k : ℝ)
  have hδ : 0 < δ := div_pos hε hkpos
  have hC : 0 < 1 + 1 / δ := by positivity
  refine ⟨(1 + 1 / δ) ^ k, pow_pos hC _, ?_⟩
  intro X hX
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hbase : 1 + Real.log X ≤ (1 + 1 / δ) * X ^ δ := by
    calc
      _ ≤ X ^ δ + X ^ δ / δ :=
        add_le_add (Real.one_le_rpow hX hδ.le) (Real.log_le_rpow_div hX0 hδ)
      _ = _ := by ring
  calc
    _ ≤ ((1 + 1 / δ) * X ^ δ) ^ k :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hX]) hbase k
    _ = (1 + 1 / δ) ^ k * (X ^ δ) ^ k := mul_pow _ _ _
    _ = (1 + 1 / δ) ^ k * X ^ ε := by
      rw [← Real.rpow_mul_natCast hX0]
      have hδk : δ * (k : ℝ) = ε := div_mul_cancel₀ ε (ne_of_gt hkpos)
      rw [hδk]

end QuaternaryQuadraticForms
