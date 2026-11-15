import QuaternaryQuadraticForms.HeathBrownIntegralDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Internal quadratic hypotheses for the source integral estimates

The Hessian below is the matrix of the derivative of the actual gradient.
Its equality with twice the symmetric coefficient matrix, its determinant,
and the common positive determinant bound are proved internally. The final
lemma selects one derivative-bound sequence for a uniformly bounded family
of actual complex weights.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The displayed linear gradient has its literal constant Fréchet derivative. -/
theorem realQuadraticGradient_hasFDerivAt
    (A : Matrix (Fin 4) (Fin 4) ℝ) (x : RealVector4) :
    HasFDerivAt (realQuadraticGradient A)
      ((2 : ℝ) • A.toEuclideanLin.toContinuousLinearMap) x := by
  simpa only [realQuadraticGradient, LinearMap.coe_toContinuousLinearMap'] using
    (A.toEuclideanLin.toContinuousLinearMap.hasFDerivAt (x := x)).fun_const_smul
      (2 : ℝ)

/-- The actual Hessian of a symmetric quadratic form is exactly `2 A`. -/
theorem realHessian_realQuadraticValue
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (x : RealVector4) :
    realHessian (realQuadraticValue A) x = (2 : ℝ) • A := by
  have hgrad : gradient (realQuadraticValue A) = realQuadraticGradient A :=
    funext (gradient_realQuadraticValue A hA)
  ext i j
  simp [realHessian, hgrad, (realQuadraticGradient_hasFDerivAt A x).fderiv,
    Matrix.toEuclideanLin_apply]

/-- Determinant of the actual four-dimensional Hessian. -/
theorem det_realHessian_realQuadraticValue
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (x : RealVector4) :
    (realHessian (realQuadraticValue A) x).det = (2 : ℝ) ^ 4 * A.det := by
  rw [realHessian_realQuadraticValue A hA, Matrix.det_smul]
  simp only [Fintype.card_fin]

/-- Its absolute determinant is independent of the point. -/
theorem abs_det_realHessian_realQuadraticValue
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (x : RealVector4) :
    |(realHessian (realQuadraticValue A) x).det| = (2 : ℝ) ^ 4 * |A.det| := by
  rw [det_realHessian_realQuadraticValue A hA, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 4)]

/-- Nonsingularity supplies one strictly positive Hessian determinant bound
at every point, hence on every weight support. -/
theorem realQuadraticValue_hessian_uniform_lower_bound
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : RealVector4,
      η ≤ |(realHessian (realQuadraticValue A) x).det| := by
  refine ⟨(2 : ℝ) ^ 4 * |A.det|,
    mul_pos (by norm_num) (abs_pos.mpr hdet), ?_⟩
  intro x
  rw [abs_det_realHessian_realQuadraticValue A hA]

/-- Extract a common positive bound sequence before selecting an individual
weight. This is the quantitative source-class hypothesis needed for a family. -/
theorem exists_uniformHBWeightControl
    (𝒲 : Set (RealVector4 → ℂ)) (B : ℝ)
    (hweight : ∀ w ∈ 𝒲, IsSmoothWeight w)
    (hsupport : ∀ w ∈ 𝒲, ∀ x ∈ tsupport w, ‖x‖ ≤ B)
    (hderiv : UniformCoordinateDerivatives 𝒲) :
    ∃ D : ℕ → ℝ, (∀ k : ℕ, 0 < D k) ∧ ∀ w ∈ 𝒲, HBWeightControl B D w := by
  let D : ℕ → ℝ := fun k => Classical.choose (hderiv k)
  refine ⟨D, ?_, ?_⟩
  · intro k
    exact (Classical.choose_spec (hderiv k)).1
  · intro w hw
    refine ⟨hweight w hw, hsupport w hw, ?_⟩
    intro k x I
    exact (Classical.choose_spec (hderiv k)).2 w hw x I

end QuaternaryQuadraticForms
