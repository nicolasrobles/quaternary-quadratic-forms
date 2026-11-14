import QuaternaryQuadraticForms.ConicCharts
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial coordinates and derivatives of the conic parametrization

These are the actual binary quadratic coordinate forms. Their evaluations
are identified with the projective parametrization, and their formal partial
derivatives are identified with its two independent tangent vectors.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MvPolynomial

variable {K : Type*} [Field K]

/-- The three binary quadratic coordinate polynomials. -/
def canonicalConicPolynomials (a : K) : Fin 3 → MvPolynomial (Fin 2) K :=
  ![C (-a) * X 0 ^ 2, X 1 ^ 2, X 0 * X 1]

/-- Evaluation recovers the literal quadratic parametrization. -/
theorem canonicalConicPolynomials_eval (a : K) (v : Fin 2 → K) :
    (fun i => eval v (canonicalConicPolynomials a i)) = canonicalConicVector a v := by
  ext i
  fin_cases i <;> simp [canonicalConicPolynomials, canonicalConicVector]

/-- Each coordinate polynomial is homogeneous of degree two. -/
theorem canonicalConicPolynomials_homogeneous (a : K) (i : Fin 3) :
    (canonicalConicPolynomials a i).IsHomogeneous 2 := by
  fin_cases i
  · exact isHomogeneous_C_mul_X_pow (-a) 0 2
  · exact isHomogeneous_X_pow 1 2
  · exact (isHomogeneous_X K 0).mul (isHomogeneous_X K 1)

/-- The evaluated first partials are the explicit first tangent vector. -/
theorem canonicalConicPolynomials_partial_s (a : K) (v : Fin 2 → K) :
    (fun i => eval v (pderiv 0 (canonicalConicPolynomials a i))) =
      canonicalConicDs a v := by
  ext i
  fin_cases i <;>
    simp [canonicalConicPolynomials, canonicalConicDs]
  ring

/-- The evaluated second partials are the explicit second tangent vector. -/
theorem canonicalConicPolynomials_partial_t (a : K) (v : Fin 2 → K) :
    (fun i => eval v (pderiv 1 (canonicalConicPolynomials a i))) =
      canonicalConicDt v := by
  ext i
  fin_cases i <;>
    simp [canonicalConicPolynomials, canonicalConicDt]

/-- The actual polynomial partial derivatives are independent at every
nonzero parameter, provided the characteristic is not two. -/
theorem canonicalConicPolynomials_partials_independent (a : K) (ha : a ≠ 0)
    (h2 : (2 : K) ≠ 0) (v : Fin 2 → K) (hv : v ≠ 0) :
    LinearIndependent K
      ![(fun i => eval v (pderiv 0 (canonicalConicPolynomials a i))),
        (fun i => eval v (pderiv 1 (canonicalConicPolynomials a i)))] := by
  rw [canonicalConicPolynomials_partial_s, canonicalConicPolynomials_partial_t]
  exact canonicalConic_derivatives_independent a ha h2 v hv

/-- Coefficient extension gives the same three coordinate forms over any
extension field. -/
theorem canonicalConicPolynomials_map {L : Type*} [Field L] (f : K →+* L)
    (a : K) (i : Fin 3) :
    (canonicalConicPolynomials a i).map f = canonicalConicPolynomials (f a) i := by
  fin_cases i <;> simp [canonicalConicPolynomials]

end QuaternaryQuadraticForms
