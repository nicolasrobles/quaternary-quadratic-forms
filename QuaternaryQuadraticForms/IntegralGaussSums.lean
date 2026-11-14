import QuaternaryQuadraticForms.QuadraticGaussSums

/-!
# Integral representatives and the complete Gauss sums

These identities identify the residue-ring Gauss sum with the manuscript's
sum on integer representatives and its outer sum over reduced residues.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The quadratic value of a canonical lift reduces to the actual residue value. -/
theorem integralQuadraticValue_residueLift (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ZMod n) :
    (integralQuadraticValue A (residueLift n x) : ZMod n) =
      dotProduct x ((A.map (Int.castRingHom (ZMod n))).mulVec x) := by
  have hx : (Int.castRingHom (ZMod n)) ∘ residueLift n x = x := by
    funext i
    exact residueLift_cast n x i
  change (Int.castRingHom (ZMod n))
    (dotProduct (residueLift n x) (A.mulVec (residueLift n x))) = _
  rw [matrixQuadraticValue_map, hx]

/-- The integral Gauss sum is the literal sum on canonical integer representatives. -/
theorem integralQuadraticGaussSum_eq_lift_sum (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (u : Fin 4 → ℤ) :
    integralQuadraticGaussSum n A a u =
      ∑ x : Fin 4 → ZMod n,
        ZMod.stdAddChar ((a * integralQuadraticValue A (residueLift n x) +
          dotProduct u (residueLift n x) : ℤ) : ZMod n) := by
  unfold integralQuadraticGaussSum quadraticGaussSum
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  push_cast
  rw [integralQuadraticValue_residueLift, dotProduct_intCast]
  simp only [residueLift_cast]

/-- At zero quadratic and linear coefficient the sum is the number of vectors. -/
theorem quadraticGaussSum_zero (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) :
    quadraticGaussSum n A 0 0 = (n : ℂ) ^ 4 := by
  simp [quadraticGaussSum, AddChar.map_zero_eq_one]

/-- Modulus one contributes its single term, including in the recurrence base case. -/
theorem quadraticGaussSum_modulus_one
    (A : Matrix (Fin 4) (Fin 4) (ZMod 1)) (a : ZMod 1) (u : Fin 4 → ZMod 1) :
    quadraticGaussSum 1 A a u = 1 := by
  have hc (z : ZMod 1) : ZMod.stdAddChar z = (1 : ℂ) := by
    rw [Subsingleton.elim z 0, AddChar.map_zero_eq_one]
  simp [quadraticGaussSum, hc]

/-- The integral form of the exact modulus-one base case. -/
theorem integralQuadraticGaussSum_modulus_one
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (u : Fin 4 → ℤ) :
    integralQuadraticGaussSum 1 A a u = 1 :=
  quadraticGaussSum_modulus_one _ _ _

/-- The source's unweighted complete sum is the sum of the actual Gauss sums
over the residue-ring unit group. -/
theorem unweightedCompleteSum_eq_sum_quadraticGaussSum (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    unweightedCompleteSum n A u =
      ∑ a : (ZMod n)ˣ,
        quadraticGaussSum n (A.map (Int.castRingHom (ZMod n))) (a : ZMod n)
          (fun i => (u i : ZMod n)) := by
  unfold unweightedCompleteSum quadraticGaussSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  push_cast
  rw [integralQuadraticValue_residueLift, dotProduct_intCast]
  simp only [residueLift_cast, ZMod.natCast_zmod_val]

end QuaternaryQuadraticForms
