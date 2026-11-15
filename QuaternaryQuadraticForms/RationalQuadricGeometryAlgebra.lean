import QuaternaryQuadraticForms.ConicNormalForm

/-!
# Discriminant algebra for rational quaternary quadrics
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open Matrix

/-- A binary quadratic form with a nonzero rational zero has square discriminant. -/
theorem binary_zero_discriminant_isSquare (a b c x y : ℚ)
    (h : a * x ^ 2 + b * x * y + c * y ^ 2 = 0)
    (hne : x ≠ 0 ∨ y ≠ 0) : IsSquare (b ^ 2 - 4 * a * c) := by
  rw [isSquare_iff_exists_sq]
  by_cases hy : y = 0
  · have hx : x ≠ 0 := hne.resolve_right (not_ne_iff.mpr hy)
    have ha : a = 0 := by
      have hax : a * x ^ 2 = 0 := by simpa [hy] using h
      exact (mul_eq_zero.mp hax).resolve_right (pow_ne_zero 2 hx)
    exact ⟨b, by simp [ha]⟩
  · refine ⟨(2 * a * x + b * y) / y, ?_⟩
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hy)).mpr
    linear_combination -4 * a * h

/-- The determinant of a hyperbolic plane plus a binary form. -/
theorem det_hyperbolic_binary (a d c : ℚ) :
    Matrix.det !![(0 : ℚ), 1 / 2, 0, 0;
      1 / 2, 0, 0, 0;
      0, 0, a, d;
      0, 0, d, c] = (d ^ 2 - a * c) / 4 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- A square discriminant in a rational hyperbolic splitting would make the
original determinant a square as well. -/
theorem nonsquare_det_binary_anisotropic (D t a b c : ℚ)
    (ht : t ≠ 0) (hD : ¬ IsSquare D)
    (hdet : D * t ^ 2 = (b ^ 2 - 4 * a * c) / 16) :
    ∀ x y : ℚ, a * x ^ 2 + b * x * y + c * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro x y h
  by_contra hn
  have hne : x ≠ 0 ∨ y ≠ 0 := by tauto
  obtain ⟨u, hu⟩ := (binary_zero_discriminant_isSquare a b c x y h hne).exists_sq
  apply hD
  rw [isSquare_iff_exists_sq]
  refine ⟨u / (4 * t), ?_⟩
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) ht))).mpr
  rw [hu] at hdet
  nlinarith [hdet]

end QuaternaryQuadraticForms
