import QuaternaryQuadraticForms.CompleteSumAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring

/-!
# Square completion for a matrix quadratic form

The identity is over an arbitrary commutative ring. The scalar `b` is an
actual inverse of `4 * a * det A`; the translation uses the adjugate of
the given matrix. No field structure or diagonalization is assumed.
-/

noncomputable section

namespace QuaternaryQuadraticForms

private theorem matrix_pairing_symm {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (hA : A.transpose = A)
    (x y : Fin 4 → R) :
    dotProduct x (A.mulVec y) = dotProduct y (A.mulVec x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

private theorem adjugate_mulVec_ring {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (u : Fin 4 → R) :
    A.mulVec (A.adjugate.mulVec u) = A.det • u := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- The source square-completion substitution over any commutative ring,
with an actual inverse of `4*a*det A`. -/
theorem matrix_quadratic_square_completion {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) (hA : A.transpose = A)
    (a b : R) (u x : Fin 4 → R) (hb : (4 * a * A.det) * b = 1) :
    a * dotProduct (x - (2 * b) • A.adjugate.mulVec u)
        (A.mulVec (x - (2 * b) • A.adjugate.mulVec u)) +
      dotProduct u (x - (2 * b) • A.adjugate.mulVec u) =
    a * dotProduct x (A.mulVec x) - b * dotProduct u (A.adjugate.mulVec u) := by
  have hc : dotProduct (A.adjugate.mulVec u) (A.mulVec x) =
      A.det * dotProduct u x := by
    rw [matrix_pairing_symm A hA, adjugate_mulVec_ring, dotProduct_smul,
      smul_eq_mul, dotProduct_comm x u]
  calc
    _ = a * dotProduct x (A.mulVec x) +
        (1 - (4 * a * A.det) * b) * dotProduct u x +
        ((4 * a * A.det) * b - 2) * b *
          dotProduct u (A.adjugate.mulVec u) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, adjugate_mulVec_ring,
        sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      rw [hc, dotProduct_comm x u, dotProduct_comm (A.adjugate.mulVec u) u]
      ring
    _ = _ := by rw [hb]; ring

end QuaternaryQuadraticForms
