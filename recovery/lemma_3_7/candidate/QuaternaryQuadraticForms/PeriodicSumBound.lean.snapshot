import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Uniform bounds for periodic partial sums

A complex-valued sequence with a positive period, zero sum over one
period, and termwise norm at most one has every initial partial sum
bounded by the period. The period is independent of the cutoff.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Removing complete periods bounds every initial partial sum by the
fixed period. No condition on the value at zero is required. -/
theorem periodic_sum_range_norm_le (f : ℕ → ℂ) (P : ℕ) (hP : 0 < P)
    (hperiod : Function.Periodic f P)
    (hzero : ∑ n ∈ Finset.range P, f n = 0)
    (hnorm : ∀ n : ℕ, ‖f n‖ ≤ 1) (T : ℕ) :
    ‖∑ n ∈ Finset.range T, f n‖ ≤ (P : ℝ) := by
  induction T using Nat.strong_induction_on with
  | h T ih =>
    by_cases hT : T < P
    · calc
        ‖∑ n ∈ Finset.range T, f n‖ ≤ ∑ n ∈ Finset.range T, ‖f n‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => hnorm n
        _ = (T : ℝ) := by simp
        _ ≤ (P : ℝ) := Nat.cast_le.mpr hT.le
    · have hPT : P ≤ T := Nat.le_of_not_gt hT
      have hsplit := Finset.sum_range_add f P (T - P)
      rw [Nat.add_sub_of_le hPT, hzero, zero_add] at hsplit
      have hreduce : (∑ n ∈ Finset.range T, f n) =
          ∑ n ∈ Finset.range (T - P), f n := by
        rw [hsplit]
        apply Finset.sum_congr rfl
        intro n _
        rw [Nat.add_comm, hperiod n]
      rw [hreduce]
      exact ih (T - P) (Nat.sub_lt (hP.trans_le hPT) hP)

end QuaternaryQuadraticForms
