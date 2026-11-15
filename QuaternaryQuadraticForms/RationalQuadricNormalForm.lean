import QuaternaryQuadraticForms.RationalQuadricGeometryAlgebra
import QuaternaryQuadraticForms.RationalQuadricGeometryBasis

/-!
# Rational normal form for the nonsplit quaternary quadric

A nondegenerate rational quaternary form with a rational isotropic vector
contains a hyperbolic plane. If its determinant is not a rational square,
the remaining binary form is anisotropic. The exact transformation below is
the geometric input to the lattice count in Lemma 2.3.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open Matrix

/-- The exact rational normal form, with an anisotropic binary complement,
used to count integral zeros of a quaternary form of nonsquare determinant. -/
theorem exists_rational_quadric_normal_form
    (S : Matrix (Fin 4) (Fin 4) ℚ) (hS : S.transpose = S) (hdet : S.det ≠ 0)
    (hns : ¬ IsSquare S.det)
    (hiso : ∃ e : Fin 4 → ℚ, e ≠ 0 ∧ dotProduct e (S.mulVec e) = 0) :
    ∃ (T : Matrix (Fin 4) (Fin 4) ℚ) (a b c : ℚ),
      T.det ≠ 0 ∧
      (∀ y : Fin 4 → ℚ,
        dotProduct (T.mulVec y) (S.mulVec (T.mulVec y)) =
          y 0 * y 1 + a * y 2 ^ 2 + b * y 2 * y 3 + c * y 3 ^ 2) ∧
      (∀ x y : ℚ, a * x ^ 2 + b * x * y + c * y ^ 2 = 0 → x = 0 ∧ y = 0) := by
  obtain ⟨T, a, d, c, hT, hcong⟩ := exists_rational_hyperbolic_matrix S hS hdet hiso
  have hd : S.det * T.det ^ 2 = ((2 * d) ^ 2 - 4 * a * c) / 16 := by
    have hm := congrArg Matrix.det hcong
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      det_hyperbolic_binary] at hm
    calc
      S.det * T.det ^ 2 = T.det * S.det * T.det := by ring
      _ = (d ^ 2 - a * c) / 4 := hm
      _ = ((2 * d) ^ 2 - 4 * a * c) / 16 := by ring
  refine ⟨T, a, 2 * d, c, hT, ?_,
    nonsquare_det_binary_anisotropic S.det T.det a (2 * d) c hT hns hd⟩
  intro y
  calc
    dotProduct (T.mulVec y) (S.mulVec (T.mulVec y)) =
        dotProduct y ((Tᵀ * S * T).mulVec y) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec y Tᵀ, Matrix.vecMul_transpose]
    _ = y 0 * y 1 + a * y 2 ^ 2 + (2 * d) * y 2 * y 3 + c * y 3 ^ 2 := by
      rw [hcong]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
      ring

end QuaternaryQuadraticForms
