import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The exact constant and weighted subset calculation for Lemma 2.4

The expansion over subsets of prime divisors is the squarefree version of
the manuscript's totient divisor sum.  In particular, it retains the exact
constant `E + E² + ··· + Eⁿ`; no coefficient, prime, or interval parameter
enters that constant.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The exact constant in Lemma 2.4, including a zero-dimensional auxiliary value. -/
def polynomialBoxConstant : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, E => E * (1 + polynomialBoxConstant n E)

@[simp] theorem polynomialBoxConstant_zero (E : ℕ) :
    polynomialBoxConstant 0 E = 0 := rfl

theorem polynomialBoxConstant_succ (n E : ℕ) :
    polynomialBoxConstant (n + 1) E = E * (1 + polynomialBoxConstant n E) := rfl

@[simp] theorem polynomialBoxConstant_one (E : ℕ) :
    polynomialBoxConstant 1 E = E := by
  simp [polynomialBoxConstant]

/-- The recurrence is precisely the source sum of the first `n` positive powers. -/
theorem polynomialBoxConstant_eq_sum_range (n E : ℕ) :
    polynomialBoxConstant n E = ∑ i ∈ Finset.range n, E ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [polynomialBoxConstant_succ, ih, Finset.sum_range_succ']
      rw [mul_add, mul_one, Finset.mul_sum]
      simp only [← pow_succ']
      simp [add_comm]

/-- An equivalent sum indexed exactly as `E + E² + ··· + Eⁿ`. -/
theorem polynomialBoxConstant_eq_sum_Icc (n E : ℕ) :
    polynomialBoxConstant n E = ∑ i ∈ Finset.Icc 1 n, E ^ i := by
  calc
    polynomialBoxConstant n E = ∑ i ∈ Finset.range n, E ^ (i + 1) :=
      polynomialBoxConstant_eq_sum_range n E
    _ = ∑ i ∈ Finset.Ico 1 (n + 1), E ^ i := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    _ = _ := by rw [Finset.Ico_add_one_right_eq_Icc]

theorem polynomialBoxConstant_pos (n E : ℕ) (hn : 1 ≤ n) (hE : 1 ≤ E) :
    1 ≤ polynomialBoxConstant n E := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [polynomialBoxConstant_succ]
  nlinarith [Nat.zero_le (polynomialBoxConstant n E)]

/-- For a nonempty set of prime divisors, the two boundary contributions
fit inside the next exact constant. -/
theorem polynomialBox_pow_add_one_le (C : ℝ) (hC : 0 ≤ C)
    (k : ℕ) (hk : 1 ≤ k) :
    C ^ k + 1 ≤ (1 + C) ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  clear hk
  induction k with
  | zero => simp [add_comm]
  | succ k ih =>
      simp only [Nat.succ_eq_add_one] at ih
      rw [pow_succ C (k + 1), pow_succ (1 + C) (k + 1)]
      have hp : 0 ≤ (1 + C) ^ (k + 1) := pow_nonneg (by linarith) _
      have hCp : 0 ≤ C ^ (k + 1) := pow_nonneg hC _
      nlinarith [mul_le_mul_of_nonneg_right ih hC]

/-- Expand the product of the degenerate primes before summing over the base box. -/
theorem sum_polynomialBox_bad_product_eq {β : Type*} (B : Finset β)
    (S : Finset ℕ) (bad : β → Finset ℕ)
    (hbad : ∀ y ∈ B, bad y ⊆ S) :
    (∑ y ∈ B, ∏ p ∈ bad y, (p : ℝ)) =
      ∑ T ∈ S.powerset, (∏ p ∈ T, ((p : ℝ) - 1)) *
        ((B.filter fun y => T ⊆ bad y).card : ℝ) := by
  classical
  have hpoint (y : β) (hy : y ∈ B) :
      (∏ p ∈ bad y, (p : ℝ)) =
        ∑ T ∈ S.powerset, if T ⊆ bad y then ∏ p ∈ T, ((p : ℝ) - 1) else 0 := by
    rw [← Finset.sum_filter]
    have hfilter : S.powerset.filter (fun T => T ⊆ bad y) = (bad y).powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans (hbad y hy), h⟩⟩
    rw [hfilter, ← Finset.prod_add_one]
    simp
  rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- The first subset product bound in the manuscript. -/
theorem polynomialBox_subset_ratio_sum_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) (C : ℝ) (hC : 0 ≤ C) :
    (∑ T ∈ S.powerset,
      (∏ p ∈ T, ((p : ℝ) - 1)) * C ^ T.card / (∏ p ∈ T, (p : ℝ))) ≤
      (1 + C) ^ S.card := by
  have heq :
      (∑ T ∈ S.powerset,
        (∏ p ∈ T, ((p : ℝ) - 1)) * C ^ T.card / (∏ p ∈ T, (p : ℝ))) =
      ∏ p ∈ S, (1 + C * ((p : ℝ) - 1) / (p : ℝ)) := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T hT
    simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  rw [heq]
  calc
    (∏ p ∈ S, (1 + C * ((p : ℝ) - 1) / (p : ℝ))) ≤ ∏ _p ∈ S, (1 + C) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
        have hpm : 0 ≤ (p : ℝ) - 1 := by linarith
        exact add_nonneg zero_le_one (div_nonneg (mul_nonneg hC hpm) (by positivity))
      · intro p hp
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
        have hpos : (0 : ℝ) < p := by linarith
        apply add_le_add_left
        apply (div_le_iff₀ hpos).2
        nlinarith
    _ = (1 + C) ^ S.card := by simp

/-- The second subset product bound, retaining the product of all primes. -/
theorem polynomialBox_subset_weight_sum_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) (C : ℝ) (hC : 1 ≤ C) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, ((p : ℝ) - 1)) * C ^ T.card) ≤
      C ^ S.card * (∏ p ∈ S, (p : ℝ)) := by
  have heq :
      (∑ T ∈ S.powerset, (∏ p ∈ T, ((p : ℝ) - 1)) * C ^ T.card) =
      ∏ p ∈ S, (1 + C * ((p : ℝ) - 1)) := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T hT
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  rw [heq]
  calc
    (∏ p ∈ S, (1 + C * ((p : ℝ) - 1))) ≤ ∏ p ∈ S, C * (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
        have hpm : 0 ≤ (p : ℝ) - 1 := by linarith
        exact add_nonneg zero_le_one (mul_nonneg (by linarith) hpm)
      · intro p hp
        nlinarith
    _ = C ^ S.card * (∏ p ∈ S, (p : ℝ)) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- The weighted degeneracy sum supplied by the induction hypothesis. -/
theorem sum_polynomialBox_bad_product_le {β : Type*} (B : Finset β)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (bad : β → Finset ℕ)
    (hbad : ∀ y ∈ B, bad y ⊆ S) (C Y : ℝ) (hC : 1 ≤ C) (hY : 0 ≤ Y)
    (d : ℕ)
    (hdeg : ∀ T ⊆ S,
      ((B.filter fun y => T ⊆ bad y).card : ℝ) ≤
        C ^ T.card * (Y ^ d / (∏ p ∈ T, (p : ℝ)) + Y ^ (d - 1))) :
    (∑ y ∈ B, ∏ p ∈ bad y, (p : ℝ)) ≤
      Y ^ d * (1 + C) ^ S.card +
        Y ^ (d - 1) * (C ^ S.card * (∏ p ∈ S, (p : ℝ))) := by
  classical
  rw [sum_polynomialBox_bad_product_eq B S bad hbad]
  calc
    (∑ T ∈ S.powerset, (∏ p ∈ T, ((p : ℝ) - 1)) *
        ((B.filter fun y => T ⊆ bad y).card : ℝ)) ≤
      ∑ T ∈ S.powerset, (∏ p ∈ T, ((p : ℝ) - 1)) *
        (C ^ T.card * (Y ^ d / (∏ p ∈ T, (p : ℝ)) + Y ^ (d - 1))) := by
      apply Finset.sum_le_sum
      intro T hT
      have hTS := Finset.mem_powerset.mp hT
      apply mul_le_mul_of_nonneg_left (hdeg T hTS)
      apply Finset.prod_nonneg
      intro p hp
      have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hS p (hTS hp)
      linarith
    _ = Y ^ d *
        (∑ T ∈ S.powerset,
          (∏ p ∈ T, ((p : ℝ) - 1)) * C ^ T.card / (∏ p ∈ T, (p : ℝ))) +
        Y ^ (d - 1) *
        (∑ T ∈ S.powerset, (∏ p ∈ T, ((p : ℝ) - 1)) * C ^ T.card) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (polynomialBox_subset_ratio_sum_le S hS C (by linarith))
        (pow_nonneg hY d))
      (mul_le_mul_of_nonneg_left (polynomialBox_subset_weight_sum_le S hS C hC)
        (pow_nonneg hY (d - 1)))

/-- Summing the univariate fibre estimates gives the exact dimension-recursion
constant in Lemma 2.4. -/
theorem polynomialBox_count_step {β : Type*} (B : Finset β)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty)
    (bad : β → Finset ℕ) (hbad : ∀ y ∈ B, bad y ⊆ S)
    (E C Y : ℝ) (hE : 1 ≤ E) (hC : 1 ≤ C) (hY : 1 ≤ Y)
    (d : ℕ) (hd : 1 ≤ d) (f : β → ℝ)
    (hcard : (B.card : ℝ) ≤ Y ^ d)
    (hdeg : ∀ T ⊆ S,
      ((B.filter fun y => T ⊆ bad y).card : ℝ) ≤
        C ^ T.card * (Y ^ d / (∏ p ∈ T, (p : ℝ)) + Y ^ (d - 1)))
    (hf : ∀ y ∈ B,
      f y ≤ E ^ S.card *
        (Y * (∏ p ∈ bad y, (p : ℝ)) / (∏ p ∈ S, (p : ℝ)) + 1)) :
    (∑ y ∈ B, f y) ≤
      (E * (1 + C)) ^ S.card * (Y ^ (d + 1) / (∏ p ∈ S, (p : ℝ)) + Y ^ d) := by
  classical
  let M : ℝ := ∏ p ∈ S, (p : ℝ)
  have hM : 0 < M := by
    apply Finset.prod_pos
    intro p hp
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    linarith
  have hE0 : 0 ≤ E := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hsum := sum_polynomialBox_bad_product_le B S hS bad hbad C Y hC hY0 d hdeg
  have hpow := polynomialBox_pow_add_one_le C (by linarith) S.card
    (Finset.card_pos.mpr hne)
  have hYsucc : Y * Y ^ d = Y ^ (d + 1) := by ring
  have hYpred : Y * Y ^ (d - 1) = Y ^ d := by
    rw [← pow_succ']
    congr 1
    omega
  calc
    (∑ y ∈ B, f y) ≤
        ∑ y ∈ B, E ^ S.card * (Y * (∏ p ∈ bad y, (p : ℝ)) / M + 1) :=
      Finset.sum_le_sum hf
    _ = E ^ S.card *
        (Y / M * (∑ y ∈ B, ∏ p ∈ bad y, (p : ℝ)) + (B.card : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ E ^ S.card *
        (Y / M * (Y ^ d * (1 + C) ^ S.card +
          Y ^ (d - 1) * (C ^ S.card * M)) + Y ^ d) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hE0 _)
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (div_nonneg hY0 hM.le)) hcard
    _ = E ^ S.card *
        ((1 + C) ^ S.card * Y ^ (d + 1) / M + (C ^ S.card + 1) * Y ^ d) := by
      congr 1
      calc
        Y / M * (Y ^ d * (1 + C) ^ S.card +
            Y ^ (d - 1) * (C ^ S.card * M)) + Y ^ d =
            (1 + C) ^ S.card * (Y * Y ^ d) / M +
              C ^ S.card * (Y * Y ^ (d - 1)) + Y ^ d := by
          field_simp [hM.ne']
        _ = _ := by rw [hYsucc, hYpred]; ring
    _ ≤ E ^ S.card *
        ((1 + C) ^ S.card * Y ^ (d + 1) / M + (1 + C) ^ S.card * Y ^ d) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hE0 _)
      exact add_le_add_left (mul_le_mul_of_nonneg_right hpow (pow_nonneg hY0 d)) _
    _ = _ := by rw [mul_pow]; ring

end QuaternaryQuadraticForms
