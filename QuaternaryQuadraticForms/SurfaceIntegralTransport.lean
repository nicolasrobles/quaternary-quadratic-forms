import QuaternaryQuadraticForms.SurfaceIntegralDefinitions
import QuaternaryQuadraticForms.SignedCoordinateChanges

/-!
# Orthogonal transport of the actual singular integral

The normalized three-dimensional Hausdorff measure, its restriction to
the actual zero set, and the gradient denominator are all transported
by the same Euclidean isometry. No surface-integral invariance premise
or chart-integral substitute is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory

/-- Orthogonal maps preserve the actual normalized Euclidean surface
measure, by invariance of Hausdorff measure under isometries. -/
theorem euclideanSurfaceMeasure_realIsometry
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    MeasurePreserving e euclideanSurfaceMeasure euclideanSurfaceMeasure := by
  exact (e.toIsometryEquiv.measurePreserving_hausdorffMeasure 3).smul_measure _

/-- Restricting the actual surface measure commutes with the inverse
image under an orthogonal map. This holds for every set. -/
theorem euclideanSurfaceMeasure_restrict_realIsometry
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) (s : Set RealVector4) :
    MeasurePreserving e
      (euclideanSurfaceMeasure.restrict (e ⁻¹' s))
      (euclideanSurfaceMeasure.restrict s) :=
  (euclideanSurfaceMeasure_realIsometry e).restrict_preimage_emb
    e.toMeasurableEquiv.measurableEmbedding s

/-- Absolute integrability of the literal singular-integral integrand
is equivalent before and after an orthogonal change of coordinates. -/
theorem singularIntegral_integrable_comp_realIsometry
    (F : RealVector4 → ℝ) (hF : Differentiable ℝ F)
    (w : RealVector4 → ℂ) (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    Integrable
      (fun x => w (e x) / (‖gradient (fun y => F (e y)) x‖ : ℂ))
      (euclideanSurfaceMeasure.restrict {x | F (e x) = 0}) ↔
    Integrable (fun x => w x / (‖gradient F x‖ : ℂ))
      (euclideanSurfaceMeasure.restrict {x | F x = 0}) := by
  simp_rw [norm_gradient_comp_realIsometry F e _ (hF _)]
  exact (euclideanSurfaceMeasure_restrict_realIsometry e {x | F x = 0}).integrable_comp_emb
    (g := fun x : RealVector4 => w x / (‖gradient F x‖ : ℂ))
    e.toMeasurableEquiv.measurableEmbedding

/-- The source singular integral is invariant under the actual
orthogonal changes of variables used for localized weights. -/
theorem singularIntegral_comp_realIsometry
    (F : RealVector4 → ℝ) (hF : Differentiable ℝ F)
    (w : RealVector4 → ℂ) (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    singularIntegral (fun x => F (e x)) (fun x => w (e x)) =
      singularIntegral F w := by
  unfold singularIntegral
  simp_rw [norm_gradient_comp_realIsometry F e _ (hF _)]
  exact (euclideanSurfaceMeasure_restrict_realIsometry e {x | F x = 0}).integral_comp
    e.toMeasurableEquiv.measurableEmbedding
    (fun x => w x / (‖gradient F x‖ : ℂ))

end QuaternaryQuadraticForms
