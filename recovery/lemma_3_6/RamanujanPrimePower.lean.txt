import QuaternaryQuadraticForms.RamanujanMultiplicativity
import QuaternaryQuadraticForms.PrimePowerUnitDigits

/-!
# Exact prime-power Ramanujan sums

The actual unit-digit bijection and additive orthogonality give the
recurrence, including both possible divisibility cases. Induction then
evaluates the literal unit sum at every positive prime-power exponent.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem ramanujan_digit_orthogonality (p : ℕ) [NeZero p] (m : ℤ) :
    (∑ t : ZMod p, ZMod.stdAddChar (((t.val : ℤ) * m : ℤ) : ZMod p)) =
      if (p : ℤ) ∣ m then (p : ℂ) else 0 := by
  classical
  simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    ZMod.card, apply_ite, Nat.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] using
    AddChar.sum_mulShift (m : ZMod p) (ZMod.isPrimitive_stdAddChar p)

private theorem ramanujan_digit_phase (p c : ℕ) [NeZero p] [NeZero c]
    (a t m : ℤ) :
    ZMod.stdAddChar (((a + (c : ℤ) * t) * m : ℤ) : ZMod (p * c)) =
      ZMod.stdAddChar ((a * m : ℤ) : ZMod (p * c)) *
        ZMod.stdAddChar ((t * m : ℤ) : ZMod p) := by
  rw [show (a + (c : ℤ) * t) * m = a * m + (c : ℤ) * (t * m) by ring]
  rw [Int.cast_add, AddChar.map_add_eq_mul, stdAddChar_mul_modulus]

private theorem ramanujan_unit_digits (p c : ℕ) [NeZero p] [NeZero c]
    (hpc : p ∣ c) (m : ℤ) :
    integralRamanujanSum (p * c) m =
      (∑ a : (ZMod c)ˣ,
        ZMod.stdAddChar (((((a : ZMod c).val : ℤ) * m : ℤ)) : ZMod (p * c))) *
          (if (p : ℤ) ∣ m then (p : ℂ) else 0) := by
  classical
  rw [integralRamanujanSum_eq_lift_sum,
    sum_units_residueLift_digits c p hpc
      (fun a => ZMod.stdAddChar ((a * m : ℤ) : ZMod (p * c)))]
  simp_rw [ramanujan_digit_phase, ← Finset.mul_sum, ramanujan_digit_orthogonality]
  rw [Finset.sum_mul]

/-- The two exact values of the actual integral Ramanujan sum at a prime. -/
theorem integralRamanujanSum_prime_eq (p : ℕ) [Fact p.Prime] (m : ℤ) :
    integralRamanujanSum p m = if (p : ℤ) ∣ m then (p : ℂ) - 1 else -1 := by
  simp only [integralRamanujanSum, residueRamanujanSum_prime, primeRamanujan_eq,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A repeated modulus factor kills the actual unit sum when it does not
divide the frequency. Primality of the factor is unnecessary. -/
theorem integralRamanujanSum_mul_modulus_eq_zero (p c : ℕ)
    [NeZero p] [NeZero c] (hpc : p ∣ c) (m : ℤ) (hpm : ¬(p : ℤ) ∣ m) :
    integralRamanujanSum (p * c) m = 0 := by
  rw [ramanujan_unit_digits p c hpc m, if_neg hpm, mul_zero]

/-- Divisibility of the frequency gives the exact unit-digit recurrence.
The proof uses the literal positive standard character at both moduli. -/
theorem integralRamanujanSum_mul_modulus_mul (p c : ℕ)
    [NeZero p] [NeZero c] (hpc : p ∣ c) (m : ℤ) :
    integralRamanujanSum (p * c) ((p : ℤ) * m) =
      (p : ℂ) * integralRamanujanSum c m := by
  rw [ramanujan_unit_digits p c hpc ((p : ℤ) * m), if_pos (dvd_mul_right _ _),
    mul_comm, integralRamanujanSum_eq_lift_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [show (((a : ZMod c).val : ℤ) * ((p : ℤ) * m)) =
    (p : ℤ) * (((a : ZMod c).val : ℤ) * m) by ring]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  field_simp

/-- The exact prime-power unit sum, with no valuation convention required
at zero frequency. The exponent is every positive integer. -/
theorem integralRamanujanSum_prime_power_eq (p k : ℕ) [Fact p.Prime] (m : ℤ) :
    integralRamanujanSum (p ^ (k + 1)) m =
      if ((p : ℤ) ^ (k + 1)) ∣ m then (p : ℂ) ^ k * ((p : ℂ) - 1)
      else if ((p : ℤ) ^ k) ∣ m then -(p : ℂ) ^ k else 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction k generalizing m with
  | zero => simpa only [zero_add, pow_one, pow_zero, one_dvd, if_true, one_mul] using
      integralRamanujanSum_prime_eq p m
  | succ k ih =>
    by_cases hpm : (p : ℤ) ∣ m
    · obtain ⟨z, rfl⟩ := hpm
      have hrec : integralRamanujanSum (p ^ (k + 1 + 1)) ((p : ℤ) * z) =
          (p : ℂ) * integralRamanujanSum (p ^ (k + 1)) z := by
        simpa only [pow_succ' p (k + 1)] using
          integralRamanujanSum_mul_modulus_mul p (p ^ (k + 1))
            (dvd_pow_self p (by omega)) z
      rw [hrec, ih]
      have htop : (p : ℤ) ^ (k + 1 + 1) ∣ (p : ℤ) * z ↔
          (p : ℤ) ^ (k + 1) ∣ z := by
        rw [pow_succ', mul_dvd_mul_iff_left hpz]
      have hlow : (p : ℤ) ^ (k + 1) ∣ (p : ℤ) * z ↔ (p : ℤ) ^ k ∣ z := by
        rw [pow_succ', mul_dvd_mul_iff_left hpz]
      simp only [htop, hlow]
      split_ifs <;> simp [pow_succ] <;> ring
    · have hrec : integralRamanujanSum (p ^ (k + 1 + 1)) m = 0 := by
        simpa only [pow_succ' p (k + 1)] using
          integralRamanujanSum_mul_modulus_eq_zero p (p ^ (k + 1))
            (dvd_pow_self p (by omega)) m hpm
      have htop : ¬(p : ℤ) ^ (k + 1 + 1) ∣ m :=
        fun h => hpm ((dvd_pow_self (p : ℤ) (by omega)).trans h)
      have hlow : ¬(p : ℤ) ^ (k + 1) ∣ m :=
        fun h => hpm ((dvd_pow_self (p : ℤ) (by omega)).trans h)
      rw [hrec, if_neg htop, if_neg hlow]

end QuaternaryQuadraticForms
