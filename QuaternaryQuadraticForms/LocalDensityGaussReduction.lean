import QuaternaryQuadraticForms.LocalDensityDefinitions
import QuaternaryQuadraticForms.PrimePowerScalarDecomposition

/-!
# Exact reduction of the scalar sums in the local density count

Cancelling a common scalar and modulus factor leaves four free residue digits.
Together with the unit/multiple partition this gives the finite recurrence for
the full additive-character count, without a nonsingularity or odd-prime condition.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Cancelling the factor `n` in the scalar coefficient and modulus leaves
exactly `n^4` vector lifts. Both positive moduli may have common prime factors. -/
theorem integralQuadraticGaussSum_scaled_modulus (m n : ℕ) [NeZero m] [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) :
    integralQuadraticGaussSum (m * n) A ((n : ℤ) * a) 0 =
      (n : ℂ) ^ 4 * integralQuadraticGaussSum m A a 0 := by
  classical
  simp only [integralQuadraticGaussSum_eq_lift_sum, zero_dotProduct, add_zero]
  simp_rw [mul_assoc, stdAddChar_mul_modulus]
  rw [sum_residueLift_digits m n (fun x => ZMod.stdAddChar (N := m)
    ((a * integralQuadraticValue A x : ℤ) : ZMod m))]
  have hphase (r : Fin 4 → ZMod m) (s : Fin 4 → ZMod n) :
      ZMod.stdAddChar (N := m)
        ((a * integralQuadraticValue A
          (fun i => residueLift m r i + (m : ℤ) * residueLift n s i) : ℤ) : ZMod m) =
      ZMod.stdAddChar (N := m)
        ((a * integralQuadraticValue A (residueLift m r) : ℤ) : ZMod m) := by
    congr 1
    push_cast
    rw [integralQuadraticValue_congr_mod m A _ (residueLift m r)
      (fun i => by simp)]
  simp_rw [hphase]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
  rw [← Finset.mul_sum]

/-- The full scalar Gauss sum at the next prime power consists of the unit
complete sum and `p^4` times the preceding full scalar Gauss sum. -/
theorem primePower_fullGauss_recurrence (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (∑ a : ZMod (p ^ (k + 1)),
      quadraticGaussSum (p ^ (k + 1)) (A.map (Int.castRingHom _)) a 0) =
      unweightedCompleteSum (p ^ (k + 1)) A 0 +
        (p : ℂ) ^ 4 * ∑ b : ZMod (p ^ k),
          quadraticGaussSum (p ^ k) (A.map (Int.castRingHom _)) b 0 := by
  classical
  have h :
      (∑ a : ZMod (p ^ k * p),
        quadraticGaussSum (p ^ k * p) (A.map (Int.castRingHom _)) a 0) =
        unweightedCompleteSum (p ^ k * p) A 0 +
          (p : ℂ) ^ 4 * ∑ b : ZMod (p ^ k),
            quadraticGaussSum (p ^ k) (A.map (Int.castRingHom _)) b 0 := by
    rw [sum_primePower_scalars]
    rw [unweightedCompleteSum_eq_sum_quadraticGaussSum]
    simp only [Pi.zero_apply, Int.cast_zero]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simpa only [integralQuadraticGaussSum, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val, Pi.zero_apply, Int.cast_zero] using
      integralQuadraticGaussSum_scaled_modulus (p ^ k) p A (b.val : ℤ)
  simpa only [pow_succ] using h

end QuaternaryQuadraticForms
