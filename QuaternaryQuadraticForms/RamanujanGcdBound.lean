import QuaternaryQuadraticForms.RamanujanPrimePower
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree

/-!
# Gcd bounds and shared-prime vanishing for the actual Ramanujan sums

Prime-power evaluation and actual CRT imply the gcd bound. A squared
prime factor in the modulus forces vanishing unless that prime divides
the frequency. Squarefreeness then gives the exact source indicator.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The exact prime-power evaluation implies the gcd bound, including
zero frequency and the modulus-one boundary. -/
theorem integralRamanujanSum_prime_power_norm_le_gcd (p k : ℕ)
    [Fact p.Prime] (m : ℤ) :
    ‖integralRamanujanSum (p ^ k) m‖ ≤ (Nat.gcd (p ^ k) m.natAbs : ℝ) := by
  have hp : p.Prime := Fact.out
  cases k with
  | zero => simp [integralRamanujanSum_modulus_one]
  | succ k =>
    rw [integralRamanujanSum_prime_power_eq]
    by_cases htop : (p : ℤ) ^ (k + 1) ∣ m
    · rw [if_pos htop]
      have htopN : p ^ (k + 1) ∣ m.natAbs :=
        Int.natCast_dvd.mp (by simpa only [Nat.cast_pow] using htop)
      rw [Nat.gcd_eq_left htopN, Nat.cast_pow]
      have hpR : 0 ≤ (p : ℝ) - 1 := by
        have h : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
        linarith
      have hnorm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
        have heq : (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) := by simp
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpR]
      rw [norm_mul, norm_pow, Complex.norm_natCast, hnorm, pow_succ]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one)
        (pow_nonneg (Nat.cast_nonneg p) k)
    · rw [if_neg htop]
      by_cases hlow : (p : ℤ) ^ k ∣ m
      · rw [if_pos hlow, norm_neg, norm_pow, Complex.norm_natCast]
        have hlowN : p ^ k ∣ m.natAbs :=
          Int.natCast_dvd.mp (by simpa only [Nat.cast_pow] using hlow)
        have hdiv : p ^ k ∣ Nat.gcd (p ^ (k + 1)) m.natAbs :=
          Nat.dvd_gcd (pow_dvd_pow p (Nat.le_succ k)) hlowN
        have hpos : 0 < Nat.gcd (p ^ (k + 1)) m.natAbs :=
          Nat.gcd_pos_of_pos_left m.natAbs (pow_pos hp.pos _)
        exact_mod_cast Nat.le_of_dvd hpos hdiv
      · rw [if_neg hlow, norm_zero]
        exact Nat.cast_nonneg _

/-- The norm of the literal Ramanujan unit sum is bounded by the actual
gcd of the modulus and frequency. No coprimality or nonzero-frequency
condition is imposed. -/
theorem integralRamanujanSum_norm_le_gcd (n : ℕ) [NeZero n] (m : ℤ) :
    ‖integralRamanujanSum n m‖ ≤ (Nat.gcd n m.natAbs : ℝ) := by
  have hall : ∀ (n : ℕ) (hn : n ≠ 0),
      ‖@integralRamanujanSum n ⟨hn⟩ m‖ ≤ (Nat.gcd n m.natAbs : ℝ) := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p k hp _ _
      letI : Fact p.Prime := ⟨hp⟩
      exact integralRamanujanSum_prime_power_norm_le_gcd p k m
    · intro hzero
      exact (hzero rfl).elim
    · intro _
      simp [integralRamanujanSum_modulus_one]
    · intro a b _ _ hab iha ihb hab0
      letI : NeZero a := ⟨left_ne_zero_of_mul hab0⟩
      letI : NeZero b := ⟨right_ne_zero_of_mul hab0⟩
      have hgcd : Nat.gcd (a * b) m.natAbs =
          Nat.gcd a m.natAbs * Nat.gcd b m.natAbs := by
        simpa only [Nat.gcd_comm] using hab.gcd_mul m.natAbs
      rw [integralRamanujanSum_mul a b hab m, norm_mul, hgcd, Nat.cast_mul]
      exact mul_le_mul (iha (NeZero.ne a)) (ihb (NeZero.ne b))
        (norm_nonneg _) (Nat.cast_nonneg _)
  exact hall n (NeZero.ne n)

/-- Multiplying the modulus by a positive integer costs at most that
integer in the gcd estimate. -/
theorem integralRamanujanSum_mul_norm_le (d c : ℕ) [NeZero d] [NeZero c]
    (m : ℤ) :
    ‖integralRamanujanSum (d * c) m‖ ≤ (d : ℝ) * (Nat.gcd c m.natAbs : ℝ) := by
  apply (integralRamanujanSum_norm_le_gcd (d * c) m).trans
  have hdiv : Nat.gcd (d * c) m.natAbs ∣ d * Nat.gcd c m.natAbs :=
    (Nat.gcd_mul_left_dvd_mul_gcd m.natAbs d c).trans
      (Nat.mul_dvd_mul (Nat.gcd_dvd_left d m.natAbs) dvd_rfl)
  have hpos : 0 < d * Nat.gcd c m.natAbs := Nat.mul_pos
    (Nat.pos_of_ne_zero (NeZero.ne d))
    (Nat.gcd_pos_of_pos_left m.natAbs (Nat.pos_of_ne_zero (NeZero.ne c)))
  exact_mod_cast Nat.le_of_dvd hpos hdiv

/-- A squared prime factor of the modulus forces the literal unit sum
to vanish unless that prime divides the frequency. -/
theorem integralRamanujanSum_eq_zero_of_prime_sq_dvd (n : ℕ) [NeZero n]
    (m : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ^ 2 ∣ n)
    (hpm : ¬(p : ℤ) ∣ m) : integralRamanujanSum n m = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨t, hnt⟩ := hp2
  have ht : t ≠ 0 := by
    intro ht0
    exact NeZero.ne n (by simpa only [ht0, mul_zero] using hnt)
  letI : NeZero t := ⟨ht⟩
  have heq : p * (p * t) = n := by
    rw [hnt, pow_two, Nat.mul_assoc]
  have hs := integralRamanujanSum_mul_modulus_eq_zero p (p * t)
    (dvd_mul_right p t) m hpm
  simpa only [heq] using hs

/-- For a squarefree shared factor, the repeated-prime vanishing gives
the exact divisibility condition used in Lemma 3.6. -/
theorem integralRamanujanSum_shared_eq_zero (d c : ℕ) [NeZero d] [NeZero c]
    (hd : Squarefree d) (hdc : d ∣ c) (m : ℤ) (hm : ¬(d : ℤ) ∣ m) :
    integralRamanujanSum (d * c) m = 0 := by
  by_contra hR
  apply hm
  apply Int.natCast_dvd.mpr
  have hg : Squarefree (Nat.gcd d m.natAbs) :=
    hd.squarefree_of_dvd (Nat.gcd_dvd_left d m.natAbs)
  have heq : d = Nat.gcd d m.natAbs := by
    apply (Nat.Squarefree.ext_iff hd hg).mpr
    intro p hp
    constructor
    · intro hpd
      apply Nat.dvd_gcd hpd
      by_contra hpm
      have hp2 : p ^ 2 ∣ d * c := by
        simpa only [pow_two] using Nat.mul_dvd_mul hpd (hpd.trans hdc)
      exact hR (integralRamanujanSum_eq_zero_of_prime_sq_dvd (d * c) m p hp hp2
        (fun h => hpm (Int.natCast_dvd.mp h)))
    · exact fun h => h.trans (Nat.gcd_dvd_left d m.natAbs)
  rw [heq]
  exact Nat.gcd_dvd_right d m.natAbs

/-- The norm estimate with the full shared-factor divisibility indicator. -/
theorem integralRamanujanSum_shared_norm_le (d c : ℕ) [NeZero d] [NeZero c]
    (hd : Squarefree d) (hdc : d ∣ c) (m : ℤ) :
    ‖integralRamanujanSum (d * c) m‖ ≤
      if (d : ℤ) ∣ m then (d : ℝ) * (Nat.gcd c m.natAbs : ℝ) else 0 := by
  split_ifs with hm
  · exact integralRamanujanSum_mul_norm_le d c m
  · rw [integralRamanujanSum_shared_eq_zero d c hd hdc m hm, norm_zero]

end QuaternaryQuadraticForms
