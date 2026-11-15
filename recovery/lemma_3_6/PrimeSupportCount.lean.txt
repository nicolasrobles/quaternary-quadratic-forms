import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting positive moduli with prescribed prime support

The finite set contains exactly the positive integers up to the cutoff
whose prime divisors all divide the specified nonzero integer. Their
actual factorization vectors inject into a finite box. This proves the
logarithmic count used before Lemma 3.6, including the factor one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual positive moduli up to a natural cutoff with prime support
contained in the prime support of `N`. -/
def primeSupportModuliUpTo (N T : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 T).filter (fun b => ∀ p : ℕ, p.Prime → p ∣ b → p ∣ N)

/-- Membership retains positivity, the cutoff, and the literal condition
on every prime divisor. -/
theorem mem_primeSupportModuliUpTo (N T b : ℕ) :
    b ∈ primeSupportModuliUpTo N T ↔
      1 ≤ b ∧ b ≤ T ∧ (∀ p : ℕ, p.Prime → p ∣ b → p ∣ N) := by
  classical
  simp only [primeSupportModuliUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

private theorem factorization_le_log_two {b T p : ℕ}
    (hb : 1 ≤ b) (hbT : b ≤ T) (hp : p.Prime) :
    b.factorization p ≤ Nat.log 2 T := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact (Nat.pow_le_pow_left hp.two_le _).trans
    ((Nat.ordProj_le p (Nat.one_le_iff_ne_zero.mp hb)).trans hbT)

private theorem factorization_eq_zero_outside_support {N b p : ℕ}
    (hN : N ≠ 0) (hb : ∀ r : ℕ, r.Prime → r ∣ b → r ∣ N)
    (hp : p ∉ N.primeFactors) : b.factorization p = 0 := by
  by_cases hprime : p.Prime
  · apply Nat.factorization_eq_zero_of_not_dvd
    intro hpb
    exact hp (Nat.mem_primeFactors.mpr ⟨hprime, hb p hprime hpb, hN⟩)
  · exact Nat.factorization_eq_zero_of_non_prime b hprime

/-- Actual exponent vectors give the finite-box bound for all positive
moduli supported on the primes dividing `N`. -/
theorem primeSupportModuliUpTo_card_le (N T : ℕ) (hN : N ≠ 0) :
    (primeSupportModuliUpTo N T).card ≤
      (Nat.log 2 T + 1) ^ N.primeFactors.card := by
  classical
  let encode : {b // b ∈ primeSupportModuliUpTo N T} →
      (p : N.primeFactors) → Fin (Nat.log 2 T + 1) := fun b p =>
    ⟨b.val.factorization p.val, Nat.lt_succ_of_le
      (factorization_le_log_two
        ((mem_primeSupportModuliUpTo N T b.val).mp b.property).1
        ((mem_primeSupportModuliUpTo N T b.val).mp b.property).2.1
        (Nat.prime_of_mem_primeFactors p.property))⟩
  have hinj : Function.Injective encode := by
    intro b c hbc
    apply Subtype.ext
    have hb := (mem_primeSupportModuliUpTo N T b.val).mp b.property
    have hc := (mem_primeSupportModuliUpTo N T c.val).mp c.property
    apply Nat.eq_of_factorization_eq
      (Nat.one_le_iff_ne_zero.mp hb.1) (Nat.one_le_iff_ne_zero.mp hc.1)
    intro p
    by_cases hp : p ∈ N.primeFactors
    · exact congrArg Fin.val (congrFun hbc ⟨p, hp⟩)
    · rw [factorization_eq_zero_outside_support hN hb.2.2 hp,
        factorization_eq_zero_outside_support hN hc.2.2 hp]
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hinj

/-- The exact logarithmic bound in the source, with an arbitrary real
cutoff at least one and the actual finite prime support of `N`. -/
theorem primeSupportModuliUpTo_card_le_log (N : ℕ) (hN : N ≠ 0)
    (X : ℝ) (hX : 1 ≤ X) :
    ((primeSupportModuliUpTo N ⌊X⌋₊).card : ℝ) ≤
      (1 + Real.log X / Real.log 2) ^ N.primeFactors.card := by
  have hfloor : 0 < (⌊X⌋₊ : ℝ) := by
    exact_mod_cast Nat.floor_pos.mpr hX
  have hlog : (Nat.log 2 ⌊X⌋₊ : ℝ) ≤ Real.log X / Real.log 2 := by
    calc
      _ ≤ Real.logb 2 (⌊X⌋₊ : ℝ) := by
        simpa only [Nat.cast_ofNat] using Real.natLog_le_logb ⌊X⌋₊ 2
      _ ≤ Real.log X / Real.log 2 := by
        unfold Real.logb
        exact div_le_div_of_nonneg_right
          (Real.log_le_log hfloor (Nat.floor_le (zero_le_one.trans hX)))
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  calc
    _ ≤ (((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ)) ^ N.primeFactors.card := by
      exact_mod_cast primeSupportModuliUpTo_card_le N ⌊X⌋₊ hN
    _ ≤ (1 + Real.log X / Real.log 2) ^ N.primeFactors.card := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_right hlog 1

/-- A normalized logarithmic count with a constant depending only on
the fixed prime support, suitable for uniform power absorption. -/
theorem primeSupportModuliUpTo_card_le_log_normalized (N : ℕ) (hN : N ≠ 0)
    (X : ℝ) (hX : 1 ≤ X) :
    ((primeSupportModuliUpTo N ⌊X⌋₊).card : ℝ) ≤
      (1 + (Real.log 2)⁻¹) ^ N.primeFactors.card *
        (1 + Real.log X) ^ N.primeFactors.card := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hinv : 0 ≤ (Real.log (2 : ℝ))⁻¹ := inv_nonneg.mpr hlogtwo.le
  have hbase : 1 + Real.log X / Real.log 2 ≤
      (1 + (Real.log 2)⁻¹) * (1 + Real.log X) := by
    rw [div_eq_mul_inv]
    nlinarith
  calc
    _ ≤ (1 + Real.log X / Real.log 2) ^ N.primeFactors.card :=
      primeSupportModuliUpTo_card_le_log N hN X hX
    _ ≤ ((1 + (Real.log 2)⁻¹) * (1 + Real.log X)) ^ N.primeFactors.card :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := mul_pow _ _ _

end QuaternaryQuadraticForms
