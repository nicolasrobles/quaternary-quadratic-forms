import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The uniform divisor bound

The actual number of positive divisors is bounded by every positive
real power, with a constant chosen independently of the integer.
The proof uses the prime-factorization product for the divisor count.
Large primes contribute no constant; the finitely many small primes
are controlled uniformly by Bernoulli's inequality.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem exponent_add_one_le_geometric (r : ℝ) (hr : 1 < r) (k : ℕ) :
    (k : ℝ) + 1 ≤ (1 + 1 / (r - 1)) * r ^ k := by
  have hd : 0 < r - 1 := sub_pos.mpr hr
  have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ r by linarith) k
  have hk : (k : ℝ) ≤ r ^ k / (r - 1) :=
    (le_div_iff₀ hd).mpr (by linarith)
  calc
    _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
    _ = _ := by ring

/-- The number of positive divisors grows more slowly than every
prescribed positive real power, with a positive constant uniform in `n`. -/
theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let D : ℝ := 1 + 1 / (r - 1)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (sub_nonneg.mpr hr.le))
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨B, hB⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  have hlarge (p : ℕ) (hp : B ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    have hbase : (2 : ℝ) ^ ε⁻¹ ≤ (p : ℝ) :=
      hB.le.trans (by exact_mod_cast hp)
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ ε⁻¹) hbase hε.le
    simpa only [Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.ne'] using h
  refine ⟨D ^ B, pow_pos hDpos _, ?_⟩
  intro n hn
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < B then D else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < B
    · rw [if_pos hsmall]
      calc
        _ ≤ D * r ^ n.factorization p := exponent_add_one_le_geometric r hr _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity : 0 ≤ r)
            (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _) hDpos.le
    · rw [if_neg hsmall, one_mul]
      calc
        _ ≤ (2 : ℝ) ^ n.factorization p := by
          simpa only [mul_one, one_add_one_eq_two, add_comm] using
            (one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) (n.factorization p))
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) (hlarge p (Nat.le_of_not_gt hsmall)) _
  have hsmallcard : (n.primeFactors.filter (fun p => p < B)).card ≤ B := by
    calc
      _ ≤ (Finset.range B).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = B := Finset.card_range B
  have hcorrection : (∏ p ∈ n.primeFactors, if p < B then D else 1) ≤ D ^ B := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    exact pow_le_pow_right₀ hD hsmallcard
  have hfactor_nat : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
    Nat.factorization_prod_pow_eq_self hn.ne'
  have hfactor : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
    exact_mod_cast hfactor_nat
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    calc
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := by
        apply Finset.prod_congr rfl
        intro p _
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
          mul_comm ε (n.factorization p : ℝ),
          Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ ε :=
        Real.finset_prod_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ε
      _ = _ := congrArg (fun x : ℝ => x ^ ε) hfactor
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn.ne', Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < B then D else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod (fun _ _ => by positivity) hprime
    _ = (∏ p ∈ n.primeFactors, if p < B then D else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ D ^ B * (n : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hcorrection (Real.rpow_nonneg (Nat.cast_nonneg n) ε)

end QuaternaryQuadraticForms
