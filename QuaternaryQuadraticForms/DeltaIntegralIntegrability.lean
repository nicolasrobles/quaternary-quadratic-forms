import QuaternaryQuadraticForms.QuadraticSingularNormalization
import QuaternaryQuadraticForms.SurfaceIntegralTransport

/-!
# Absolute integrability for localized quadratic weight families

The actual surface integrand is integrable whenever every weight admits
one of the source C₀ coordinate descriptions.  The proof transports the
internally established chart integrability through the actual Euclidean
isometry.  No integrability assertion at a cone vertex is assumed.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory

/-- A coordinate cover by controlled C₀ weights proves absolute
integrability of the original, literal quadratic surface integrand. -/
theorem quadraticFamily_singularIntegral_integrable_of_isometry_cover
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (weights : Set (RealVector4 → ℂ))
    (B : ℝ) (D : ℕ → ℝ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hcover : ∀ w ∈ weights, ∃ s : SignedCoordinateChange,
      HBC0Control (fun x => realQuadraticValue A (signedCoordinateIsometry s x))
        B D a lam (fun x => w (signedCoordinateIsometry s x))) :
    ∀ w ∈ weights,
      IntegrableOn (fun x => w x / (‖gradient (realQuadraticValue A) x‖ : ℂ))
        {x : RealVector4 | realQuadraticValue A x = 0} euclideanSurfaceMeasure := by
  intro w hw
  obtain ⟨s, hs⟩ := hcover w hw
  let e := signedCoordinateIsometry s
  let A' := realQuadraticPullbackMatrix A e
  have hA' : A'.transpose = A' := realQuadraticPullbackMatrix_symmetric A hA e
  have hF' : realQuadraticValue A' = fun x => realQuadraticValue A (e x) :=
    funext (realQuadraticPullbackMatrix_value A e)
  have hcontrol : HBC0Control (realQuadraticValue A') B D a lam (fun x => w (e x)) := by
    rw [hF']
    exact hs
  have hi := quadraticC0_singularIntegral_integrable_of_geometry
    A' hA' (fun x => w (e x)) hcontrol.1.1 a lam ha hlam hcontrol.2
  rw [hF'] at hi
  exact (singularIntegral_integrable_comp_realIsometry (realQuadraticValue A)
    ((realQuadraticValue_contDiff A).differentiable (by simp)) w e).mp hi

end QuaternaryQuadraticForms
