import QuaternaryQuadraticForms.QuadraticGaussSums
import QuaternaryQuadraticForms.MatrixSquareCompletion

/-!
# Exact translation of quadratic Gauss sums

Square completion is implemented by a bijection of the actual residue
vectors. The inverse in the final phase is the standard inverse in
`ZMod n`, justified by its unit hypothesis even when `n = 1`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Translation by the adjugate vector removes the linear term, with any
actual inverse of `4*a*det A` and the manuscript's exact phase. -/
theorem quadraticGaussSum_shift_of_inverse (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (hA : A.transpose = A)
    (a b : ZMod n) (u : Fin 4 → ZMod n)
    (hb : (4 * a * A.det) * b = 1) :
    quadraticGaussSum n A a u =
      ZMod.stdAddChar (-b * dotProduct u (A.adjugate.mulVec u)) *
        quadraticGaussSum n A a 0 := by
  let s : Fin 4 → ZMod n := (2 * b) • A.adjugate.mulVec u
  calc
    quadraticGaussSum n A a u =
        ∑ x : Fin 4 → ZMod n,
          ZMod.stdAddChar
            (a * dotProduct (x - s) (A.mulVec (x - s)) + dotProduct u (x - s)) := by
      exact (Equiv.sum_comp (Equiv.subRight s)
        (fun x : Fin 4 → ZMod n =>
          ZMod.stdAddChar (a * dotProduct x (A.mulVec x) + dotProduct u x))).symm
    _ = ∑ x : Fin 4 → ZMod n,
        ZMod.stdAddChar
          (a * dotProduct x (A.mulVec x) - b * dotProduct u (A.adjugate.mulVec u)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show a * dotProduct (x - s) (A.mulVec (x - s)) + dotProduct u (x - s) =
          a * dotProduct x (A.mulVec x) - b * dotProduct u (A.adjugate.mulVec u)
        from matrix_quadratic_square_completion A hA a b u x hb]
    _ = _ := by
      simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
      rw [← Finset.sum_mul]
      simp only [quadraticGaussSum, zero_dotProduct, add_zero, neg_mul]
      rw [mul_comm]

/-- The exact shifted Gauss sum with the literal modular inverse in the
source phase; no field structure is required on the residue ring. -/
theorem quadraticGaussSum_shift (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (hA : A.transpose = A)
    (a : ZMod n) (u : Fin 4 → ZMod n)
    (hunit : IsUnit (4 * a * A.det)) :
    quadraticGaussSum n A a u =
      ZMod.stdAddChar (-(4 * a * A.det)⁻¹ * dotProduct u (A.adjugate.mulVec u)) *
        quadraticGaussSum n A a 0 :=
  quadraticGaussSum_shift_of_inverse n A hA a (4 * a * A.det)⁻¹ u
    (ZMod.mul_inv_of_unit _ hunit)

/-- Separate unit hypotheses on `2`, the scalar, and the determinant
supply exactly the modular inverse needed for square completion. -/
theorem quadraticGaussSum_shift_of_units (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (hA : A.transpose = A)
    (a : ZMod n) (u : Fin 4 → ZMod n)
    (h2 : IsUnit (2 : ZMod n)) (ha : IsUnit a) (hdet : IsUnit A.det) :
    quadraticGaussSum n A a u =
      ZMod.stdAddChar (-(4 * a * A.det)⁻¹ * dotProduct u (A.adjugate.mulVec u)) *
        quadraticGaussSum n A a 0 := by
  apply quadraticGaussSum_shift n A hA a u
  have h4 : IsUnit (4 : ZMod n) := by
    convert h2.mul h2 using 1
    norm_num
  exact (h4.mul ha).mul hdet

end QuaternaryQuadraticForms
