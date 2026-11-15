import QuaternaryQuadraticForms.PeriodicSumBound
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring

/-!
# Cubic weights and periodic cancellation

Finite summation by parts turns the uniform bound for the actual
partial sums of a periodic complex sequence into a cubic weighted
bound. The estimate includes the empty cutoff and does not require
the sequence to vanish at zero, since the cubic weight does.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A zero-mean periodic sequence of norm at most one has cubic
weighted sums bounded by twice its period times the cutoff cubed. -/
theorem periodic_cubic_sum_norm_le (f : ℕ → ℂ) (P : ℕ) (hP : 0 < P)
    (hperiod : Function.Periodic f P)
    (hzero : ∑ n ∈ Finset.range P, f n = 0)
    (hnorm : ∀ n : ℕ, ‖f n‖ ≤ 1) (T : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 T, f n * (n : ℂ) ^ 3‖ ≤
      2 * (P : ℝ) * (T : ℝ) ^ 3 := by
  have hprefix (n : ℕ) : ‖∑ i ∈ Finset.range n, f i‖ ≤ (P : ℝ) :=
    periodic_sum_range_norm_le f P hP hperiod hzero hnorm n
  have hdiff (n : ℕ) : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 - (n : ℝ) ^ 3 := by
    apply sub_nonneg.mpr
    exact pow_le_pow_left₀ (Nat.cast_nonneg n)
      (Nat.cast_le.mpr (Nat.le_succ n)) 3
  have hinterval : (∑ n ∈ Finset.Icc 1 T, f n * (n : ℂ) ^ 3) =
      ∑ n ∈ Finset.range (T + 1), (n : ℝ) ^ 3 • f n := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sub (fun n : ℕ => f n * (n : ℂ) ^ 3)
        (show 1 ≤ T + 1 from Nat.succ_le_succ (Nat.zero_le T))]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0),
      mul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_natCast, mul_comm]
  have hparts := Finset.sum_range_by_parts (fun n : ℕ => (n : ℝ) ^ 3) f (T + 1)
  simp only [Nat.add_sub_cancel] at hparts
  have hboundary : ‖(T : ℝ) ^ 3 • ∑ n ∈ Finset.range (T + 1), f n‖ ≤
      (T : ℝ) ^ 3 * (P : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg T) 3)]
    exact mul_le_mul_of_nonneg_left (hprefix (T + 1))
      (pow_nonneg (Nat.cast_nonneg T) 3)
  have hvariation :
      ‖∑ n ∈ Finset.range T,
        (((n + 1 : ℕ) : ℝ) ^ 3 - (n : ℝ) ^ 3) •
          ∑ i ∈ Finset.range (n + 1), f i‖ ≤
      ∑ n ∈ Finset.range T,
        (((n + 1 : ℕ) : ℝ) ^ 3 - (n : ℝ) ^ 3) * (P : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro n _
    rw [norm_smul, Real.norm_of_nonneg (hdiff n)]
    exact mul_le_mul_of_nonneg_left (hprefix (n + 1)) (hdiff n)
  calc
    _ = ‖(T : ℝ) ^ 3 • ∑ n ∈ Finset.range (T + 1), f n -
        ∑ n ∈ Finset.range T,
          (((n + 1 : ℕ) : ℝ) ^ 3 - (n : ℝ) ^ 3) •
            ∑ i ∈ Finset.range (n + 1), f i‖ := by rw [hinterval, hparts]
    _ ≤ ‖(T : ℝ) ^ 3 • ∑ n ∈ Finset.range (T + 1), f n‖ +
        ‖∑ n ∈ Finset.range T,
          (((n + 1 : ℕ) : ℝ) ^ 3 - (n : ℝ) ^ 3) •
            ∑ i ∈ Finset.range (n + 1), f i‖ := norm_sub_le _ _
    _ ≤ (T : ℝ) ^ 3 * (P : ℝ) + ∑ n ∈ Finset.range T,
        (((n + 1 : ℕ) : ℝ) ^ 3 - (n : ℝ) ^ 3) * (P : ℝ) :=
      add_le_add hboundary hvariation
    _ = 2 * (P : ℝ) * (T : ℝ) ^ 3 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun n : ℕ => (n : ℝ) ^ 3) T]
      simp only [Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), sub_zero]
      ring

/-- The same cubic estimate for a nonnegative real cutoff. In
particular it includes cutoffs below one, whose sum is empty. -/
theorem periodic_cubic_sum_floor_norm_le (f : ℕ → ℂ) (P : ℕ) (hP : 0 < P)
    (hperiod : Function.Periodic f P)
    (hzero : ∑ n ∈ Finset.range P, f n = 0)
    (hnorm : ∀ n : ℕ, ‖f n‖ ≤ 1) (Z : ℝ) (hZ : 0 ≤ Z) :
    ‖∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, f n * (n : ℂ) ^ 3‖ ≤
      2 * (P : ℝ) * Z ^ 3 := by
  refine (periodic_cubic_sum_norm_le f P hP hperiod hzero hnorm ⌊Z⌋₊).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg ⌊Z⌋₊) (Nat.floor_le hZ) 3)
    (mul_nonneg zero_le_two (Nat.cast_nonneg P))

end QuaternaryQuadraticForms
