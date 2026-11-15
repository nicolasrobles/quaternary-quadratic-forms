import QuaternaryQuadraticForms.AnalyticDefinitions
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real quadratic geometry for the integral estimates

The actual matrix expression is smooth. For a symmetric matrix its actual
gradient is `2 A x`, and nonsingularity makes this vector nonzero away from
the origin. Compactness then supplies a uniform positive gradient bound on
every closed annulus whose inner radius is positive. These are internal
deductions; no geometric or analytic literature premise is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped ContDiff
open InnerProductSpace

/-- The literal matrix expression agrees with the Euclidean inner product. -/
theorem realQuadraticValue_eq_inner (A : Matrix (Fin 4) (Fin 4) ℝ)
    (x : RealVector4) :
    realQuadraticValue A x = inner ℝ x (A.toEuclideanLin x) := by
  simp only [realQuadraticValue, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, star_trivial]
  exact dotProduct_comm _ _

/-- The actual real quadratic form is infinitely differentiable. -/
theorem realQuadraticValue_contDiff (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ContDiff ℝ ∞ (realQuadraticValue A) := by
  have h : ContDiff ℝ ∞ (fun x : RealVector4 => inner ℝ x (A.toEuclideanLin x)) := by
    simpa only [LinearMap.coe_toContinuousLinearMap', id_eq] using
      (contDiff_id : ContDiff ℝ ∞ (id : RealVector4 → RealVector4)).inner ℝ
        A.toEuclideanLin.toContinuousLinearMap.contDiff
  simpa only [← realQuadraticValue_eq_inner] using h

/-- In particular the matrix quadratic form is continuous. -/
theorem realQuadraticValue_continuous (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Continuous (realQuadraticValue A) :=
  (realQuadraticValue_contDiff A).continuous

/-- Literal homogeneity of degree two for every real scaling factor. -/
theorem realQuadraticValue_smul (A : Matrix (Fin 4) (Fin 4) ℝ)
    (t : ℝ) (x : RealVector4) :
    realQuadraticValue A (t • x) = t ^ 2 * realQuadraticValue A x := by
  simp only [realQuadraticValue_eq_inner, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  ring

private theorem hasGradientAt_inner_linear (T : RealVector4 →L[ℝ] RealVector4)
    (hT : (T : RealVector4 →ₗ[ℝ] RealVector4).IsSymmetric) (x : RealVector4) :
    HasGradientAt (fun y => inner ℝ y (T y)) ((2 : ℝ) • T x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd : HasFDerivAt (fun y => inner ℝ y (T y))
      ((fderivInnerCLM ℝ (x, T x)).comp
        ((ContinuousLinearMap.id ℝ RealVector4).prod T)) x := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) x).inner ℝ T.hasFDerivAt
  apply hd.congr_fderiv
  ext y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply,
    real_inner_smul_left]
  have hxy := hT x y
  simp only [ContinuousLinearMap.coe_coe] at hxy
  linarith [real_inner_comm y (T x)]

/-- The displayed vector `2 A x` is the actual derivative gradient. -/
theorem realQuadraticValue_hasGradientAt (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A.transpose = A) (x : RealVector4) :
    HasGradientAt (realQuadraticValue A) (realQuadraticGradient A x) x := by
  have hs : A.toEuclideanLin.IsSymmetric := by
    apply Matrix.isHermitian_iff_isSymmetric.mp
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have h := hasGradientAt_inner_linear A.toEuclideanLin.toContinuousLinearMap hs x
  simpa only [LinearMap.coe_toContinuousLinearMap', realQuadraticGradient,
    ← realQuadraticValue_eq_inner] using h

/-- Equality with the gradient defined by the actual Fréchet derivative. -/
theorem gradient_realQuadraticValue (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A.transpose = A) (x : RealVector4) :
    gradient (realQuadraticValue A) x = realQuadraticGradient A x :=
  (realQuadraticValue_hasGradientAt A hA x).gradient

/-- The explicit gradient vector depends continuously on the point. -/
theorem realQuadraticGradient_continuous (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Continuous (realQuadraticGradient A) :=
  A.toEuclideanLin.toContinuousLinearMap.continuous.const_smul (2 : ℝ)

/-- A nonsingular matrix has no nonzero vector with vanishing displayed gradient. -/
theorem realQuadraticGradient_ne_zero (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hdet : A.det ≠ 0) (x : RealVector4) (hx : x ≠ 0) :
    realQuadraticGradient A x ≠ 0 := by
  have hunit : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  intro hg
  have hlin : A.toEuclideanLin x = 0 := by
    simpa only [realQuadraticGradient, smul_eq_zero, OfNat.ofNat_ne_zero, false_or] using hg
  have hmul : A.mulVec (WithLp.ofLp x) = A.mulVec 0 := by
    have h := congrArg WithLp.ofLp hlin
    simpa only [Matrix.ofLp_toEuclideanLin_apply, WithLp.ofLp_zero, Matrix.mulVec_zero] using h
  have hz : WithLp.ofLp x = 0 := hinj hmul
  exact hx (WithLp.ofLp_injective 2 (by simpa only [WithLp.ofLp_zero] using hz))

/-- The closed annulus in the source Euclidean norm is compact. -/
theorem realVector4_isCompact_annulus (ρ₁ ρ₂ : ℝ) :
    IsCompact {x : RealVector4 | ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂} := by
  apply (isCompact_closedBall (0 : RealVector4) ρ₂).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

/-- One positive lower bound for `‖2 A x‖` works throughout a fixed closed
annulus separated from the origin. The bound is chosen before the point. -/
theorem realQuadraticGradient_norm_annulus_lower_bound
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : RealVector4,
      ρ₁ ≤ ‖x‖ → ‖x‖ ≤ ρ₂ → L ≤ ‖realQuadraticGradient A x‖ := by
  obtain ⟨L, hL, hb⟩ := (realVector4_isCompact_annulus ρ₁ ρ₂).exists_forall_le'
    (realQuadraticGradient_continuous A).norm.continuousOn (a := 0) (by
      intro x hx
      apply norm_pos_iff.mpr
      apply realQuadraticGradient_ne_zero A hdet
      intro hz
      have := hx.1
      rw [hz, norm_zero] at this
      exact (not_le_of_gt hρ₁) this)
  exact ⟨L, hL, fun x hx₁ hx₂ => hb x ⟨hx₁, hx₂⟩⟩

/-- The source lower bound is for the actual gradient, with symmetry
and nonsingularity checked on the actual matrix. -/
theorem gradient_realQuadraticValue_annulus_lower_bound
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : RealVector4,
      ρ₁ ≤ ‖x‖ → ‖x‖ ≤ ρ₂ → L ≤ ‖gradient (realQuadraticValue A) x‖ := by
  simpa only [gradient_realQuadraticValue A hA] using
    realQuadraticGradient_norm_annulus_lower_bound A hdet ρ₁ ρ₂ hρ₁

/-- The absolute value of the actual form is uniformly bounded on every
fixed closed ball. The positive bound is selected before the point. -/
theorem realQuadraticValue_abs_bound_closedBall
    (A : Matrix (Fin 4) (Fin 4) ℝ) (ρ : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : RealVector4, ‖x‖ ≤ ρ → |realQuadraticValue A x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : RealVector4) ρ).bddAbove_image
    (realQuadraticValue_continuous A).abs.continuousOn
  refine ⟨|M| + 1, by linarith [abs_nonneg M], ?_⟩
  intro x hx
  have hmem : x ∈ Metric.closedBall (0 : RealVector4) ρ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hb : |realQuadraticValue A x| ≤ M := hM ⟨x, hmem, rfl⟩
  linarith [le_abs_self M]

end QuaternaryQuadraticForms
