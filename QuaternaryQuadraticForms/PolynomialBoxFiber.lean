import QuaternaryQuadraticForms.PolynomialBoxDefinitions
import QuaternaryQuadraticForms.PolynomialBoxOneVariable
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp

/-!
# Degenerate primes of a polynomial fibre

At each fixed integer tail, retain exactly the primes at which the
specialized univariate polynomial is nonzero. The complementary primes
contribute the factor used in the source induction.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The primes at which the actual specialized polynomial is identically zero. -/
def polynomialBoxBadPrimes {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin (n + 1)) (ZMod p))
    (y : Fin n → ℤ) : Finset ℕ := by
  classical
  exact S.filter fun p => polynomialBoxSlice (P p) (fun i => (y i : ZMod p)) = 0

/-- Degenerate primes are always among the imposed primes. -/
theorem polynomialBoxBadPrimes_subset {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin (n + 1)) (ZMod p)) (y : Fin n → ℤ) :
    polynomialBoxBadPrimes S P y ⊆ S := by
  classical
  exact Finset.filter_subset _ _

/-- Removing identically zero congruences does not change the actual fibre. -/
theorem polynomialIntervalZeros_sdiff_bad {n : ℕ} (S : Finset ℕ)
    (P : (p : ℕ) → MvPolynomial (Fin (n + 1)) (ZMod p))
    (y : Fin n → ℤ) (a b : ℤ) :
    polynomialIntervalZeros S
        (fun p => polynomialBoxSlice (P p) (fun i => (y i : ZMod p))) a b =
      polynomialIntervalZeros (S \ polynomialBoxBadPrimes S P y)
        (fun p => polynomialBoxSlice (P p) (fun i => (y i : ZMod p))) a b := by
  classical
  ext t
  rw [mem_polynomialIntervalZeros, mem_polynomialIntervalZeros]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro ht p hp
    exact ht p (Finset.mem_sdiff.mp hp).1
  · intro ht p hp
    by_cases hb : p ∈ polynomialBoxBadPrimes S P y
    · have hzero := (Finset.mem_filter.mp hb).2
      simp only [hzero, Polynomial.eval_zero]
    · exact ht p (Finset.mem_sdiff.mpr ⟨hp, hb⟩)

/-- The one-variable estimate, with the product of degenerate primes
kept explicit, is uniform in the fixed integer tail. -/
theorem polynomialBox_fiber_card_le {n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p)
    (P : (p : ℕ) → MvPolynomial (Fin (n + 1)) (ZMod p))
    (E : ℕ) (hE : 1 ≤ E) (hdeg : ∀ p ∈ S, (P p).totalDegree ≤ E)
    (y : Fin n → ℤ) (a b : ℤ) (Y : ℝ) (hY : 0 ≤ Y)
    (hI : ((Finset.Icc a b).card : ℝ) ≤ Y) :
    ((polynomialIntervalZeros S
        (fun p => polynomialBoxSlice (P p) (fun i => (y i : ZMod p))) a b).card : ℝ) ≤
      (E : ℝ) ^ S.card *
        (Y * (∏ p ∈ polynomialBoxBadPrimes S P y, (p : ℝ)) /
          (∏ p ∈ S, (p : ℝ)) + 1) := by
  classical
  let B := polynomialBoxBadPrimes S P y
  let T := S \ B
  have hB : B ⊆ S := polynomialBoxBadPrimes_subset S P y
  have hT : T ⊆ S := Finset.sdiff_subset
  have hTP : ∀ p ∈ T,
      polynomialBoxSlice (P p) (fun i => (y i : ZMod p)) ≠ 0 := by
    intro p hp hz
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hT hp, hz⟩)
  have hbound := polynomialIntervalZeros_card_le T (fun p hp => hS p (hT hp))
    (fun p => polynomialBoxSlice (P p) (fun i => (y i : ZMod p))) E hTP
    (fun p hp => (polynomialBoxSlice_natDegree_le _ _).trans (hdeg p (hT hp)))
    a b Y hY hI
  rw [polynomialIntervalZeros_sdiff_bad S P y a b]
  have hTpos : 0 < ∏ p ∈ T, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hS p (hT hp)).pos
  have hSpos : 0 < ∏ p ∈ S, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hS p hp).pos
  have hprod : (∏ p ∈ T, (p : ℝ)) * (∏ p ∈ B, (p : ℝ)) =
      ∏ p ∈ S, (p : ℝ) := Finset.prod_sdiff hB
  have hquot : Y / (∏ p ∈ T, (p : ℝ)) =
      Y * (∏ p ∈ B, (p : ℝ)) / (∏ p ∈ S, (p : ℝ)) := by
    apply (div_eq_div_iff hTpos.ne' hSpos.ne').mpr
    rw [← hprod]
    ring
  have hpow : (E : ℝ) ^ T.card ≤ (E : ℝ) ^ S.card :=
    pow_le_pow_right₀ (by exact_mod_cast hE) (Finset.card_le_card hT)
  calc
    _ ≤ (E : ℝ) ^ T.card * (Y / (∏ p ∈ T, (p : ℝ)) + 1) := hbound
    _ ≤ (E : ℝ) ^ S.card * (Y / (∏ p ∈ T, (p : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by rw [hquot]

end QuaternaryQuadraticForms
