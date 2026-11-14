import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The coefficient calculation for a projective hypersurface

These are polynomial identities and finite-sum estimates. The geometric
adjunction and cohomological input is registered separately; no such
statement is assumed in this file.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Polynomial
open scoped BigOperators

/-- The adjunction relation through degree two, as an exact relation between
integer polynomial coefficients. -/
def SurfaceChernRelation (m : ℕ) (c : Polynomial ℤ) : Prop :=
  ∀ j ≤ 2, ((1 + C (m : ℤ) * X) * c).coeff j = ((1 + X) ^ 4).coeff j

/-- The coefficient of the surface intersection calculation, including the
degree of the hypersurface. -/
def surfaceSectionEulerCoefficient (m n : ℕ) (c : Polynomial ℤ) : ℤ :=
  (m : ℤ) * (c * (1 - C (n : ℤ) * X + C ((n : ℤ) ^ 2) * X ^ 2)).coeff 2

/-- The degree-two Chern polynomial of the quadric surface. -/
def quadricChernPolynomial : Polynomial ℤ := 1 + C (2 : ℤ) * X + C (2 : ℤ) * X ^ 2

/-- Only the first three coefficients of the Chern polynomial enter the
surface section coefficient. -/
theorem surfaceSectionEulerCoefficient_coeff (m n : ℕ) (c : Polynomial ℤ) :
    surfaceSectionEulerCoefficient m n c =
      (m : ℤ) * (c.coeff 2 - (n : ℤ) * c.coeff 1 + (n : ℤ) ^ 2 * c.coeff 0) := by
  have hpoly : c * (1 - C (n : ℤ) * X + C ((n : ℤ) ^ 2) * X ^ 2) =
      c - c * C (n : ℤ) * X + c * C ((n : ℤ) ^ 2) * X ^ 2 := by ring
  rw [surfaceSectionEulerCoefficient, hpoly]
  rw [coeff_add, coeff_sub, coeff_mul_X (c * C (n : ℤ)) 1,
    coeff_mul_X_pow' (c * C ((n : ℤ) ^ 2)) 2 2, if_pos (le_refl 2)]
  simp only [Nat.sub_self, coeff_mul_C]
  ring

/-- Adjunction determines the constant, linear, and quadratic coefficients
without imposing any condition on the higher coefficients. -/
theorem surfaceChernRelation_coefficients (m : ℕ) (c : Polynomial ℤ)
    (h : SurfaceChernRelation m c) :
    c.coeff 0 = 1 ∧ c.coeff 1 = 4 - (m : ℤ) ∧
      c.coeff 2 = (m : ℤ) ^ 2 - 4 * (m : ℤ) + 6 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  norm_num [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul,
    coeff_one_add_X_pow] at h0 h1 h2
  have hc1 : c.coeff 1 = 4 - (m : ℤ) := by
    apply eq_sub_iff_add_eq.mpr
    simpa [h0] using h1
  refine ⟨h0, hc1, ?_⟩
  calc
    c.coeff 2 = 6 - (m : ℤ) * c.coeff 1 := eq_sub_iff_add_eq.mpr h2
    _ = (m : ℤ) ^ 2 - 4 * (m : ℤ) + 6 := by rw [hc1]; ring

/-- The surface coefficient obtained from the general adjunction relation. -/
theorem surfaceSectionEulerCoefficient_of_relation (m n : ℕ) (c : Polynomial ℤ)
    (h : SurfaceChernRelation m c) :
    surfaceSectionEulerCoefficient m n c =
      (m : ℤ) * ((n : ℤ) ^ 2 + ((m : ℤ) - 4) * (n : ℤ) +
        (m : ℤ) ^ 2 - 4 * (m : ℤ) + 6) := by
  obtain ⟨h0, h1, h2⟩ := surfaceChernRelation_coefficients m c h
  rw [surfaceSectionEulerCoefficient_coeff, h0, h1, h2]
  ring

/-- The explicit quadric polynomial satisfies the adjunction relation. -/
theorem quadricChernPolynomial_relation : SurfaceChernRelation 2 quadricChernPolynomial := by
  intro j hj
  interval_cases j <;>
    norm_num [quadricChernPolynomial, add_mul, mul_assoc, coeff_add, coeff_C_mul,
      coeff_X_mul, coeff_one_add_X_pow, coeff_C_mul_X_pow, coeff_one, coeff_X, Nat.choose]

/-- The manuscript's exact quadric coefficient, with no asymptotic estimate. -/
theorem quadric_surfaceSectionEulerCoefficient (n : ℕ) :
    surfaceSectionEulerCoefficient 2 n quadricChernPolynomial =
      2 * (n : ℤ) ^ 2 - 4 * (n : ℤ) + 4 := by
  rw [surfaceSectionEulerCoefficient_of_relation 2 n quadricChernPolynomial
    quadricChernPolynomial_relation]
  ring

/-- The same quadric coefficient follows from any polynomial satisfying
the degree-two adjunction relation. -/
theorem surfaceSectionEulerCoefficient_quadric_of_relation (n : ℕ) (c : Polynomial ℤ)
    (h : SurfaceChernRelation 2 c) :
    surfaceSectionEulerCoefficient 2 n c = 2 * (n : ℤ) ^ 2 - 4 * (n : ℤ) + 4 := by
  rw [surfaceSectionEulerCoefficient_of_relation 2 n c h]
  ring

/-- A finite sum of complex numbers bounded by p has norm at most r p. -/
theorem norm_sum_le_card_mul {r : ℕ} (eigenvalues : Fin r → ℂ) (p : ℝ)
    (hbound : ∀ i, ‖eigenvalues i‖ ≤ p) :
    ‖∑ i, eigenvalues i‖ ≤ (r : ℝ) * p := by
  calc
    ‖∑ i, eigenvalues i‖ ≤ ∑ i, ‖eigenvalues i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin r, p := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (r : ℝ) * p := by simp

end QuaternaryQuadraticForms
