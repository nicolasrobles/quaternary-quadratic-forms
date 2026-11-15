import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Positivity

/-!
# A fixed constant to the number of prime factors

For every positive exponent, `C ^ omega(m)` is bounded by a constant
times `m ^ ε` on positive squarefree integers. The constant is chosen
before the modulus. Only the finitely many primes below a threshold
depending on `C` and `ε` contribute to it.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A fixed base to the number of prime factors has an arbitrarily
small positive power bound, uniformly in the squarefree modulus. -/
theorem primeFactor_pow_le_rpow (C : ℝ) (hC : 1 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m → Squarefree m →
      C ^ m.primeFactors.card ≤ K * (m : ℝ) ^ ε := by
  classical
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨B, hB⟩ := exists_nat_gt (C ^ ε⁻¹)
  have hlarge (p : ℕ) (hp : B ≤ p) : C ≤ (p : ℝ) ^ ε := by
    have hbase : C ^ ε⁻¹ ≤ (p : ℝ) := hB.le.trans (by exact_mod_cast hp)
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hCpos.le _) hbase hε.le
    simpa only [Real.rpow_inv_rpow hCpos.le hε.ne'] using h
  refine ⟨C ^ B, pow_pos hCpos _, ?_⟩
  intro m _hm hsq
  have hprime (p : ℕ) (hp : p ∈ m.primeFactors) :
      C ≤ (if p < B then C else 1) * (p : ℝ) ^ ε := by
    by_cases hsmall : p < B
    · rw [if_pos hsmall]
      have hpone : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      exact le_mul_of_one_le_right hCpos.le (Real.one_le_rpow hpone hε.le)
    · rw [if_neg hsmall, one_mul]
      exact hlarge p (Nat.le_of_not_gt hsmall)
  have hsmallcard : (m.primeFactors.filter (fun p => p < B)).card ≤ B := by
    calc
      _ ≤ (Finset.range B).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = B := Finset.card_range B
  have hcorrection : (∏ p ∈ m.primeFactors, if p < B then C else 1) ≤ C ^ B := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    exact pow_le_pow_right₀ hC hsmallcard
  have hfactor : (∏ p ∈ m.primeFactors, (p : ℝ)) = (m : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hpowers : (∏ p ∈ m.primeFactors, (p : ℝ) ^ ε) = (m : ℝ) ^ ε := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε, hfactor]
  calc
    C ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, C :=
      (Finset.prod_const C).symm
    _ ≤ ∏ p ∈ m.primeFactors, (if p < B then C else 1) * (p : ℝ) ^ ε :=
      Finset.prod_le_prod (fun _ _ => hCpos.le) hprime
    _ = (∏ p ∈ m.primeFactors, if p < B then C else 1) * (m : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ C ^ B * (m : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hcorrection (Real.rpow_nonneg (Nat.cast_nonneg m) ε)

end QuaternaryQuadraticForms
