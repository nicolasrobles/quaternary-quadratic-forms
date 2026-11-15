import QuaternaryQuadraticForms.RealQuadraticGeometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum

/-!
# Finite orthogonal coordinate changes

Coordinate permutations with independent signs form a finite family that
contains the changes used in the source localization argument. They act
on the actual Euclidean space by linear isometries, so preserve norms,
Lebesgue measure, the actual oscillatory integral, and gradient norms.
Their pullbacks are represented by nonsingular symmetric matrices.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory InnerProductSpace

/-- The finite family contains every permutation with at most one sign change. -/
abbrev SignedCoordinateChange := Equiv.Perm (Fin 4) × (Fin 4 → Bool)

/-- A signed coordinate permutation as an actual Euclidean linear isometry. -/
def signedCoordinateIsometry (s : SignedCoordinateChange) :
    RealVector4 ≃ₗᵢ[ℝ] RealVector4 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ s.1).trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 4 =>
      if s.2 i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ))

/-- The coordinates are exactly the stated permutation and signs. -/
theorem signedCoordinateIsometry_apply (s : SignedCoordinateChange)
    (x : RealVector4) (i : Fin 4) :
    signedCoordinateIsometry s x i =
      if s.2 i then -x (s.1.symm i) else x (s.1.symm i) := by
  cases hi : s.2 i <;> simp [signedCoordinateIsometry, Equiv.piCongrLeft', hi]

/-- There are only 384 coordinate changes in the chosen finite family. -/
theorem signedCoordinateChange_card : Fintype.card SignedCoordinateChange = 384 := by
  norm_num [SignedCoordinateChange, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fun, Nat.factorial]

/-- The norm used in the source is unchanged by each signed permutation. -/
theorem signedCoordinateIsometry_norm (s : SignedCoordinateChange) (x : RealVector4) :
    ‖signedCoordinateIsometry s x‖ = ‖x‖ :=
  (signedCoordinateIsometry s).norm_map x

/-- The inverse change preserves the frequency norm as well. -/
theorem signedCoordinateIsometry_symm_norm (s : SignedCoordinateChange)
    (x : RealVector4) : ‖(signedCoordinateIsometry s).symm x‖ = ‖x‖ :=
  (signedCoordinateIsometry s).symm.norm_map x

/-- Actual Lebesgue measure is preserved, with no Jacobian premise. -/
theorem signedCoordinateIsometry_measurePreserving (s : SignedCoordinateChange) :
    MeasurePreserving (signedCoordinateIsometry s) volume volume :=
  (signedCoordinateIsometry s).measurePreserving

/-- The dual frequency transforms by the inverse orthogonal map. -/
theorem real_inner_symm_isometry (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4)
    (v x : RealVector4) : inner ℝ (e.symm v) x = inner ℝ v (e x) := by
  simpa only [e.apply_symm_apply] using (e.inner_map_map (e.symm v) x).symm

/-- The actual gradient under an orthogonal change of variables. -/
theorem hasGradientAt_comp_realIsometry
    (f : RealVector4 → ℝ) (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4)
    (g x : RealVector4) (hf : HasGradientAt f g (e x)) :
    HasGradientAt (fun y => f (e y)) (e.symm g) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := hf.hasFDerivAt.comp x e.toContinuousLinearEquiv.hasFDerivAt
  apply hd.congr_fderiv
  ext y
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply]
  exact (real_inner_symm_isometry e g y).symm

/-- The derivative-defined gradient agrees with the inverse transform. -/
theorem gradient_comp_realIsometry
    (f : RealVector4 → ℝ) (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4)
    (x : RealVector4) (hf : DifferentiableAt ℝ f (e x)) :
    gradient (fun y => f (e y)) x = e.symm (gradient f (e x)) :=
  (hasGradientAt_comp_realIsometry f e _ x hf.hasGradientAt).gradient

/-- The full gradient norm, not just one coordinate derivative, is invariant. -/
theorem norm_gradient_comp_realIsometry
    (f : RealVector4 → ℝ) (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4)
    (x : RealVector4) (hf : DifferentiableAt ℝ f (e x)) :
    ‖gradient (fun y => f (e y)) x‖ = ‖gradient f (e x)‖ := by
  rw [gradient_comp_realIsometry f e x hf, e.symm.norm_map]

/-- For the actual symmetric quadratic form the inverse gradient is explicit. -/
theorem gradient_realQuadraticValue_comp_isometry
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) (x : RealVector4) :
    gradient (fun y => realQuadraticValue A (e y)) x =
      e.symm (realQuadraticGradient A (e x)) :=
  (hasGradientAt_comp_realIsometry (realQuadraticValue A) e _ x
    (realQuadraticValue_hasGradientAt A hA (e x))).gradient

/-- The coordinate matrix represents the actual linear isometry. -/
def realIsometryMatrix (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.toEuclideanLin.symm e.toLinearEquiv.toLinearMap

/-- Exact identification of the matrix action with the coordinate change. -/
theorem realIsometryMatrix_apply (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4)
    (x : RealVector4) : (realIsometryMatrix e).toEuclideanLin x = e x := by
  simp [realIsometryMatrix]

/-- Every coordinate-change matrix is nonsingular. -/
theorem realIsometryMatrix_det_ne_zero (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    (realIsometryMatrix e).det ≠ 0 := by
  have hinj : Function.Injective (realIsometryMatrix e).mulVec := by
    intro u v huv
    apply WithLp.toLp_injective 2
    apply e.injective
    rw [← realIsometryMatrix_apply e (WithLp.toLp 2 u),
      ← realIsometryMatrix_apply e (WithLp.toLp 2 v)]
    simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
    exact congrArg (WithLp.toLp 2) huv
  exact ((realIsometryMatrix e).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

/-- Matrix congruence represents the literal pullback of the form. -/
theorem realQuadraticValue_matrix_congruence
    (A P : Matrix (Fin 4) (Fin 4) ℝ) (x : RealVector4) :
    realQuadraticValue (P.transpose * A * P) x =
      realQuadraticValue A (P.toEuclideanLin x) := by
  simp only [realQuadraticValue, Matrix.ofLp_toEuclideanLin_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The actual matrix of the form after an orthogonal coordinate change. -/
def realQuadraticPullbackMatrix (A : Matrix (Fin 4) (Fin 4) ℝ)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) : Matrix (Fin 4) (Fin 4) ℝ :=
  (realIsometryMatrix e).transpose * A * realIsometryMatrix e

/-- The pullback matrix evaluates to the form composed with the actual map. -/
theorem realQuadraticPullbackMatrix_value
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) (x : RealVector4) :
    realQuadraticValue (realQuadraticPullbackMatrix A e) x = realQuadraticValue A (e x) := by
  rw [realQuadraticPullbackMatrix, realQuadraticValue_matrix_congruence,
    realIsometryMatrix_apply]

/-- Symmetry of the original matrix is preserved by the literal pullback. -/
theorem realQuadraticPullbackMatrix_symmetric
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    (realQuadraticPullbackMatrix A e).transpose = realQuadraticPullbackMatrix A e := by
  simp only [realQuadraticPullbackMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    hA, Matrix.mul_assoc]

/-- Nonsingularity is preserved; no new nondegeneracy assumption is needed. -/
theorem realQuadraticPullbackMatrix_det_ne_zero
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hdet : A.det ≠ 0)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    (realQuadraticPullbackMatrix A e).det ≠ 0 := by
  simp only [realQuadraticPullbackMatrix, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero (realIsometryMatrix_det_ne_zero e) hdet)
    (realIsometryMatrix_det_ne_zero e)

/-- Change of variables for the actual delta integral, with the source
frequency transformed by the inverse map. It holds at every real `r`. -/
theorem deltaIntegral_comp_realIsometry
    (F : RealVector4 → ℝ) (w : RealVector4 → ℂ) (r : ℝ) (v : RealVector4)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    deltaIntegral (fun x => F (e x)) (fun x => w (e x)) r (e.symm v) =
      deltaIntegral F w r v := by
  unfold deltaIntegral
  simp_rw [real_inner_symm_isometry e]
  simpa only [measureSpaceOfInnerProductSpace] using
    (e.measurePreserving.integral_comp (G := ℂ)
      e.toMeasurableEquiv.measurableEmbedding
      (fun x => w x * (heathBrownDeltaKernel (r, F x) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((-inner ℝ v x / r : ℝ) : ℂ))))

end QuaternaryQuadraticForms
