import QuaternaryQuadraticForms.RamanujanSums
import QuaternaryQuadraticForms.IntegralGaussSums
import QuaternaryQuadraticForms.IntegralGaussShift

/-!
# Summing the square-completed Gauss phases

The reciprocal coefficient permutes the actual unit group. Consequently,
a proved constant value of the unshifted Gauss sums expresses the
unweighted complete sum as that constant times its actual Ramanujan
factor. The constant Gauss value remains an explicit hypothesis of these
assembly helpers.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Summing the exact adjugate phase over the actual unit parameter gives
the original Ramanujan sum at the dual quadratic value. -/
theorem quadraticGaussSum_reciprocal_phase_sum (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (u : Fin 4 → ZMod n)
    (h2 : IsUnit (2 : ZMod n)) (hdet : IsUnit A.det) :
    (∑ a : (ZMod n)ˣ, ZMod.stdAddChar
      (-(4 * (a : ZMod n) * A.det)⁻¹ * dotProduct u (A.adjugate.mulVec u))) =
      residueRamanujanSum n (dotProduct u (A.adjugate.mulVec u)) := by
  have h4 : IsUnit (4 : ZMod n) := by
    convert h2.mul h2 using 1
    norm_num
  calc
    _ = ∑ a : (ZMod n)ˣ, ZMod.stdAddChar
        (-((4 * A.det) * (a : ZMod n))⁻¹ * dotProduct u (A.adjugate.mulVec u)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show 4 * (a : ZMod n) * A.det = (4 * A.det) * (a : ZMod n) by ring]
    _ = _ := residueRamanujanSum_reciprocal_phase n _ _ (h4.mul hdet)

/-- A constant pure Gauss value at every unit gives the exact Ramanujan
factor after the proved square completion and unit reindexing. -/
theorem sum_quadraticGaussSum_of_constant (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (hA : A.transpose = A)
    (u : Fin 4 → ZMod n) (K : ℂ)
    (h2 : IsUnit (2 : ZMod n)) (hdet : IsUnit A.det)
    (hK : ∀ a : (ZMod n)ˣ, quadraticGaussSum n A (a : ZMod n) 0 = K) :
    (∑ a : (ZMod n)ˣ, quadraticGaussSum n A (a : ZMod n) u) =
      K * residueRamanujanSum n (dotProduct u (A.adjugate.mulVec u)) := by
  calc
    _ = ∑ a : (ZMod n)ˣ, ZMod.stdAddChar
        (-(4 * (a : ZMod n) * A.det)⁻¹ * dotProduct u (A.adjugate.mulVec u)) * K := by
      apply Finset.sum_congr rfl
      intro a _
      rw [quadraticGaussSum_shift_of_units n A hA (a : ZMod n) u h2 a.isUnit hdet,
        hK a]
    _ = K * ∑ a : (ZMod n)ˣ, ZMod.stdAddChar
        (-(4 * (a : ZMod n) * A.det)⁻¹ * dotProduct u (A.adjugate.mulVec u)) := by
      rw [← Finset.sum_mul, mul_comm]
    _ = _ := by rw [quadraticGaussSum_reciprocal_phase_sum n A u h2 hdet]

/-- The same assembly for the manuscript's literal unweighted complete
sum and integral adjugate dual form. The pure-Gauss evaluation is explicit. -/
theorem unweightedCompleteSum_of_constant_gauss (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (u : Fin 4 → ℤ) (K : ℂ)
    (h2 : IsUnit (2 : ZMod n)) (hdet : IsUnit (A.det : ZMod n))
    (hK : ∀ a : (ZMod n)ˣ,
      quadraticGaussSum n (reduceQuadraticMatrix n A) (a : ZMod n) 0 = K) :
    unweightedCompleteSum n A u =
      K * integralRamanujanSum n (dotProduct u (A.adjugate.mulVec u)) := by
  have hdet' : IsUnit (reduceQuadraticMatrix n A).det := by
    have hd : (A.det : ZMod n) = (reduceQuadraticMatrix n A).det :=
      (Int.castRingHom (ZMod n)).map_det A
    rw [← hd]
    exact hdet
  have h := sum_quadraticGaussSum_of_constant n (reduceQuadraticMatrix n A)
    (reduceQuadraticMatrix_symmetric n A hA) (fun i => (u i : ZMod n)) K h2 hdet' hK
  rw [← adjugateQuadraticValue_intCast] at h
  rw [unweightedCompleteSum_eq_sum_quadraticGaussSum]
  exact h

end QuaternaryQuadraticForms
