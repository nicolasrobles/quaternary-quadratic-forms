import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Numerical constants in the Fourier bound

These elementary inequalities combine the geometric and character-sum
estimates in Lemma 4.4. They are auxiliary statements about real numbers;
the Fourier bounds require their application to the actual finite sums.
-/

namespace QuaternaryQuadraticForms

/-- The generic-plane estimates fit the constant `2 n²`. -/
theorem fourier_generic_constant_bound (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) :
    (2 * (n : ℝ) - 1) * p * Real.sqrt p +
        (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 5) * p ≤
      2 * (n : ℝ) ^ 2 * p * Real.sqrt p := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hcoeff : 0 ≤ 2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 5 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hp_sqrt : p ≤ p * Real.sqrt p := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hp) hp0
  calc
    (2 * (n : ℝ) - 1) * p * Real.sqrt p +
        (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 5) * p ≤
        (2 * (n : ℝ) - 1) * p * Real.sqrt p +
          (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 5) * (p * Real.sqrt p) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hp_sqrt hcoeff) _
    _ = (2 * (n : ℝ) ^ 2 - 2 * (n : ℝ) + 4) * (p * Real.sqrt p) := by
      ring
    _ ≤ (2 * (n : ℝ) ^ 2) * (p * Real.sqrt p) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp0 (Real.sqrt_nonneg p))
    _ = 2 * (n : ℝ) ^ 2 * p * Real.sqrt p := by ring

/-- The nonzero exceptional-plane estimates fit the constant `2 n²`. -/
theorem fourier_exceptional_constant_bound (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) :
    2 * p ^ 2 + (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 6) * p ≤
      2 * (n : ℝ) ^ 2 * p ^ 2 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hcoeff : 0 ≤ 2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 6 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hp_sq : p ≤ p ^ 2 := by
    simpa only [mul_one, ← sq] using mul_le_mul_of_nonneg_left hp hp0
  calc
    2 * p ^ 2 + (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 6) * p ≤
        2 * p ^ 2 + (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 6) * p ^ 2 :=
      add_le_add_left (mul_le_mul_of_nonneg_left hp_sq hcoeff) _
    _ = (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 8) * p ^ 2 := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * p ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg p)

/-- The zero-frequency estimate fits the constant `2 n²`. -/
theorem fourier_zero_constant_bound (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) :
    (p - 1) * (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * p ≤
      2 * (n : ℝ) ^ 2 * p ^ 2 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hcoeff : 0 ≤ 2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  calc
    (p - 1) * (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * p ≤
        p * (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * p :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hcoeff) hp0
    _ = (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * p ^ 2 := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * p ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg p)

/-- The manuscript's real exponent `3/2` equals `p * sqrt p`. -/
theorem rpow_three_halves_eq_mul_sqrt (p : ℝ) (hp : 0 ≤ p) :
    p ^ (3 / 2 : ℝ) = p * Real.sqrt p := by
  rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
    Real.rpow_add_of_nonneg hp (by norm_num) (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

end QuaternaryQuadraticForms
