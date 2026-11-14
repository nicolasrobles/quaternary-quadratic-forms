import QuaternaryQuadraticForms.GeneralPrimeGauss
import QuaternaryQuadraticForms.PrimePowerGaussRecurrence
import QuaternaryQuadraticForms.IntegralGaussShift
import QuaternaryQuadraticForms.IntegralGaussSums

/-!
# Exact Gauss evaluation at every good prime power

The prime base case and the two-step residue recurrence give the closed
pure value, including modulus one. Integral square completion then gives
the source's exact shifted formula with its adjugate dual form.
-/

noncomputable section

namespace QuaternaryQuadraticForms

private theorem integral_pure_prime
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    integralQuadraticGaussSum p A a 0 =
      (legendreSym p A.det : ℂ) * (p : ℂ) ^ 2 := by
  have ha' : (a : ZMod p) ≠ 0 :=
    fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hdet : (A.det : ZMod p) = (reduceQuadraticMatrix p A).det :=
    (Int.castRingHom (ZMod p)).map_det A
  have h := quadraticGaussSum_prime_zero_frequency p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp) (a : ZMod p) ha'
  rw [← hdet, complexQuadraticChar_intCast] at h
  simpa only [integralQuadraticGaussSum, reduceQuadraticMatrix,
    Pi.zero_apply, Int.cast_zero] using h

private theorem goodPrime_character_sq (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hp : ¬ p ∣ quadraticBadPrimeModulus A) :
    (legendreSym p A.det : ℂ) ^ 2 = 1 := by
  rw [← complexQuadraticChar_intCast]
  apply complexQuadraticChar_sq_apply p
  exact fun h => goodPrime_not_dvd_det p A hp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd A.det p).mp h)

/-- The source's pure quaternary Gauss value at every good prime power,
including the recurrence's exact modulus-one base case. -/
theorem integralQuadraticGaussSum_prime_power_pure
    (p k : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    integralQuadraticGaussSum (p ^ k) A a 0 =
      (legendreSym p A.det : ℂ) ^ k * (p : ℂ) ^ (2 * k) := by
  induction k using Nat.twoStepInduction with
  | zero =>
      simp only [pow_zero, Nat.mul_zero, integralQuadraticGaussSum_modulus_one, one_mul]
  | one =>
      simpa only [pow_one, Nat.mul_one] using integral_pure_prime p A hA hp a ha
  | more k hk _ =>
      rw [integralQuadraticGaussSum_primePower_recurrence p k (goodPrime_ne_two p A hp)
        A hA a (goodPrime_not_dvd_det p A hp) ha, hk]
      have hexp : 2 * (k + 2) = 2 * k + 4 := by omega
      rw [hexp, pow_add, goodPrime_character_sq p A hp, mul_one, pow_add]
      ring

/-- The complete shifted evaluation in Lemma 3.2(i), with the literal
integral scalar, frequency, determinant and adjugate dual form. -/
theorem integralQuadraticGaussSum_prime_power
    (p k : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : A.transpose = A) (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (u : Fin 4 → ℤ) :
    integralQuadraticGaussSum (p ^ k) A a u =
      (legendreSym p A.det : ℂ) ^ k * (p : ℂ) ^ (2 * k) *
        ZMod.stdAddChar (-((4 * a * A.det : ℤ) : ZMod (p ^ k))⁻¹ *
          ((dotProduct u (A.adjugate.mulVec u) : ℤ) : ZMod (p ^ k))) := by
  rw [integralQuadraticGaussSum_shift_prime_power p k A hA hp a ha u,
    integralQuadraticGaussSum_prime_power_pure p k A hA hp a ha]
  ring

private theorem prime_not_dvd_unit_lift
    (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (a : (ZMod (p ^ k))ˣ) :
    ¬ (p : ℤ) ∣ (((a : ZMod (p ^ k)).val : ℕ) : ℤ) := by
  have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
  let f := ZMod.castHom hpk (ZMod p)
  have hunit : IsUnit (f (a : ZMod (p ^ k))) := a.isUnit.map f
  have hcast : (((a : ZMod (p ^ k)).val : ℕ) : ZMod p) = f (a : ZMod (p ^ k)) := by
    simpa only [map_natCast] using
      congrArg f (ZMod.natCast_zmod_val (a : ZMod (p ^ k)))
  intro hdiv
  have hz : ((((a : ZMod (p ^ k)).val : ℕ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  apply hunit.ne_zero
  rw [← hcast]
  simpa only [Int.cast_natCast] using hz

/-- The same pure value for every actual unit modulo a positive prime
power, providing the constant coefficient for the Ramanujan unit sum. -/
theorem quadraticGaussSum_prime_power_units_pure
    (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (a : (ZMod (p ^ k))ˣ) :
    quadraticGaussSum (p ^ k) (reduceQuadraticMatrix (p ^ k) A) (a : ZMod (p ^ k)) 0 =
      (legendreSym p A.det : ℂ) ^ k * (p : ℂ) ^ (2 * k) := by
  have h := integralQuadraticGaussSum_prime_power_pure p k A hA hp
    (((a : ZMod (p ^ k)).val : ℕ) : ℤ) (prime_not_dvd_unit_lift p k hk a)
  simpa only [integralQuadraticGaussSum, reduceQuadraticMatrix, Pi.zero_apply,
    Int.cast_zero, Int.cast_natCast, ZMod.natCast_zmod_val] using h

end QuaternaryQuadraticForms
