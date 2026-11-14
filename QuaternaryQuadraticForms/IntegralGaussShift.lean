import QuaternaryQuadraticForms.QuadraticGaussShift
import QuaternaryQuadraticForms.PrimePowerUnits

/-!
# Square completion for the integral source form

Reduction commutes with the actual adjugate dual form. The generic residue
identity therefore has precisely the source phase `-(4aα)⁻¹ F*(u)`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The source adjugate dual value commutes with coefficient reduction. -/
theorem adjugateQuadraticValue_intCast (n : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    ((dotProduct u (A.adjugate.mulVec u) : ℤ) : ZMod n) =
      dotProduct (fun i => (u i : ZMod n))
        ((reduceQuadraticMatrix n A).adjugate.mulVec (fun i => (u i : ZMod n))) := by
  change (Int.castRingHom (ZMod n)) (dotProduct u (A.adjugate.mulVec u)) = _
  rw [matrixQuadraticValue_map, reduceQuadraticMatrix_adjugate]
  rfl

/-- Integral square completion with the exact modular inverse and dual
quadratic form occurring in the source. -/
theorem integralQuadraticGaussSum_shift (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (a : ℤ) (u : Fin 4 → ℤ)
    (hunit : IsUnit ((4 * a * A.det : ℤ) : ZMod n)) :
    integralQuadraticGaussSum n A a u =
      ZMod.stdAddChar (-((4 * a * A.det : ℤ) : ZMod n)⁻¹ *
        ((dotProduct u (A.adjugate.mulVec u) : ℤ) : ZMod n)) *
      integralQuadraticGaussSum n A a 0 := by
  have hdet : (A.det : ZMod n) = (reduceQuadraticMatrix n A).det :=
    (Int.castRingHom (ZMod n)).map_det A
  have hunit' : IsUnit (4 * (a : ZMod n) * (reduceQuadraticMatrix n A).det) := by
    simpa only [Int.cast_mul, Int.cast_ofNat, hdet] using hunit
  have h := quadraticGaussSum_shift n (reduceQuadraticMatrix n A)
    (reduceQuadraticMatrix_symmetric n A hA) (a : ZMod n)
    (fun i => (u i : ZMod n)) hunit'
  rw [← adjugateQuadraticValue_intCast, ← hdet] at h
  simpa only [integralQuadraticGaussSum, reduceQuadraticMatrix,
    Int.cast_mul, Int.cast_ofNat, Pi.zero_apply, Int.cast_zero] using h

/-- The good-prime and scalar nondivisibility hypotheses supply every unit
needed by integral square completion at each prime power. -/
theorem integralQuadraticGaussSum_shift_prime_power (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (u : Fin 4 → ℤ) :
    integralQuadraticGaussSum (p ^ k) A a u =
      ZMod.stdAddChar (-((4 * a * A.det : ℤ) : ZMod (p ^ k))⁻¹ *
        ((dotProduct u (A.adjugate.mulVec u) : ℤ) : ZMod (p ^ k))) *
      integralQuadraticGaussSum (p ^ k) A a 0 := by
  apply integralQuadraticGaussSum_shift (p ^ k) A hA a u
  have h2 := goodPrime_two_isUnit_prime_pow p k A hp
  have h4 : IsUnit (4 : ZMod (p ^ k)) := by
    convert h2.mul h2 using 1
    norm_num
  have hdet := intCast_isUnit_prime_pow p k A.det (goodPrime_not_dvd_det p A hp)
  simpa only [Int.cast_mul, Int.cast_ofNat] using
    (h4.mul (intCast_isUnit_prime_pow p k a ha)).mul hdet

end QuaternaryQuadraticForms
