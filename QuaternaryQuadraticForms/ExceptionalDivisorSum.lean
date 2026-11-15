import QuaternaryQuadraticForms.CongruenceBoxDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Divisor summation for the exceptional frequencies

The half-power weights in the actual Fourier-product expansion are summed
over the positive divisors of the squarefree second modulus.  These finite
sum estimates keep the reciprocal Euclidean norm and the literal original
polynomial indicators.  The small-power factor is bounded using the full
product modulus before summing the divisors.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Each positive divisor contributes at most the source's common shape. -/
theorem divisor_halfPower_shape_le (q₁ q₂ h : ℕ) (hq₁ : 1 ≤ q₁)
    (hh : h ∈ q₂.divisors) (U : ℝ) (hU : 0 ≤ U) :
    (h : ℝ) ^ (1 / 2 : ℝ) * (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2) ≤
      U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2 := by
  have hhpos : 0 < h := Nat.pos_of_mem_divisors hh
  have hq₂pos : 0 < q₂ := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hh).2
  have hhdiv : h ∣ q₂ := Nat.dvd_of_mem_divisors hh
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (show 1 ≤ h from hhpos)
  have hq₁pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast (show 0 < q₁ by omega)
  have hhRpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  have hhalf : (h : ℝ) ^ (1 / 2 : ℝ) ≤ (h : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hhR (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hhalf₂ : (h : ℝ) ^ (1 / 2 : ℝ) ≤ (q₂ : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg h)
      (by exact_mod_cast Nat.le_of_dvd hq₂pos hhdiv) (by norm_num)
  rw [mul_add]
  apply add_le_add
  · calc
      _ ≤ (h : ℝ) * (U ^ 3 / ((q₁ * h : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = U ^ 3 / (q₁ : ℝ) := by
        rw [Nat.cast_mul]
        field_simp [ne_of_gt hq₁pos, ne_of_gt hhRpos]
  · exact mul_le_mul_of_nonneg_right hhalf₂ (sq_nonneg U)

/-- The finite divisor sum in the source proof, including its small-power
factor, is bounded uniformly in the moduli and the real radius. -/
theorem exceptional_divisor_sum_le (q₁ q₂ : ℕ) (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (η U : ℝ) (hη : 0 ≤ η) (hU : 0 ≤ U) :
    (∑ h ∈ q₂.divisors, (h : ℝ) ^ (1 / 2 : ℝ) *
      (((q₁ * h : ℕ) : ℝ) ^ η * (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2))) ≤
      ((q₁ * q₂ : ℕ) : ℝ) ^ η * (q₂.divisors.card : ℝ) *
        (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by
  have hterm (h : ℕ) (hh : h ∈ q₂.divisors) :
      (h : ℝ) ^ (1 / 2 : ℝ) *
        (((q₁ * h : ℕ) : ℝ) ^ η * (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2)) ≤
      ((q₁ * q₂ : ℕ) : ℝ) ^ η *
        (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) := by
    have hhq₂ : h ≤ q₂ := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hh)
    have hpow : ((q₁ * h : ℕ) : ℝ) ^ η ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ η :=
      Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.mul_le_mul_left q₁ hhq₂) hη
    calc
      _ = ((q₁ * h : ℕ) : ℝ) ^ η *
          ((h : ℝ) ^ (1 / 2 : ℝ) * (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2)) := by ring
      _ ≤ ((q₁ * q₂ : ℕ) : ℝ) ^ η *
          ((h : ℝ) ^ (1 / 2 : ℝ) * (U ^ 3 / ((q₁ * h : ℕ) : ℝ) + U ^ 2)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (divisor_halfPower_shape_le q₁ q₂ h hq₁ hh U hU)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ ≤ ∑ _h ∈ q₂.divisors, ((q₁ * q₂ : ℕ) : ℝ) ^ η *
        (U ^ 3 / (q₁ : ℝ) + (q₂ : ℝ) ^ (1 / 2 : ℝ) * U ^ 2) :=
      Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Insert the actual pointwise divisor majorant into the finite weighted
sum and interchange its two finite sums. -/
theorem weightedSum_le_exceptional_divisors
    (A : Matrix (Fin 4) (Fin 4) ℤ)
    (D : (p : ℕ) → MvPolynomial (Fin 4) (ZMod p))
    (q₁ q₂ : ℕ) (U M : ℝ) (f : (Fin 4 → ℤ) → ℝ)
    (hmajor : ∀ u, f u ≤ M * ∑ h ∈ q₂.divisors,
      (h : ℝ) ^ (1 / 2 : ℝ) * exceptionalIndicator D h u) :
    (∑ u ∈ divisibleEuclideanBall A q₁ U, f u / integerEuclideanNorm u) ≤
      M * ∑ h ∈ q₂.divisors,
        (h : ℝ) ^ (1 / 2 : ℝ) * weightedCongruenceEuclideanSum A D q₁ h U := by
  classical
  calc
    _ ≤ ∑ u ∈ divisibleEuclideanBall A q₁ U,
        (M * ∑ h ∈ q₂.divisors,
          (h : ℝ) ^ (1 / 2 : ℝ) * exceptionalIndicator D h u) /
            integerEuclideanNorm u := by
      apply Finset.sum_le_sum
      intro u _hu
      exact div_le_div_of_nonneg_right (hmajor u) (integerEuclideanNorm_nonneg u)
    _ = ∑ u ∈ divisibleEuclideanBall A q₁ U, ∑ h ∈ q₂.divisors,
        M * (h : ℝ) ^ (1 / 2 : ℝ) *
          (exceptionalIndicator D h u / integerEuclideanNorm u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h _hh
      ring
    _ = ∑ h ∈ q₂.divisors, ∑ u ∈ divisibleEuclideanBall A q₁ U,
        M * (h : ℝ) ^ (1 / 2 : ℝ) *
          (exceptionalIndicator D h u / integerEuclideanNorm u) := Finset.sum_comm
    _ = _ := by
      simp only [weightedCongruenceEuclideanSum, Finset.mul_sum, mul_assoc]

end QuaternaryQuadraticForms
