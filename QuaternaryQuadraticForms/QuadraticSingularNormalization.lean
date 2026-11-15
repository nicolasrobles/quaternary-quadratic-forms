import QuaternaryQuadraticForms.QuadraticSurfaceIntegral
import QuaternaryQuadraticForms.DeltaIntegralBounds
import QuaternaryQuadraticForms.Trusted.SimonArea
import QuaternaryQuadraticForms.Trusted.HeathBrownIntegrals

/-!
# Identification of the source normalization with the actual surface integral

The separately registered general area formula is applied to the explicit
quadratic root on its open smooth domain. Heath--Brown's registered graph
limit is then identified with the actual normalized Hausdorff surface
integral by the internal quadratic bridge. No manuscript-specific graph,
Jacobian, or normalization identity is assumed.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped ContDiff Topology

/-- Simon's general area formula applies to the explicit quadratic root
on its actual open domain. No global smoothness of that root is needed. -/
theorem quadraticPositiveRoot_area_measure (A : Matrix (Fin 4) (Fin 4) ℝ) :
    euclideanSurfaceMeasure.restrict
        (surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A) =
      Measure.map (surfaceGraph (quadraticPositiveRoot A))
        ((volume.restrict (quadraticPositiveRootDomain A)).withDensity
          (fun y => ENNReal.ofReal (graphAreaFactor (quadraticPositiveRoot A) y))) :=
  Trusted.simon_graph_area _ _ (quadraticPositiveRootDomain_isOpen A)
    (quadraticPositiveRoot_measurable A)
    ((quadraticPositiveRoot_contDiffOn A).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))

/-- The source graph expression is the literal normalized surface
integral, with the general area premise now discharged by its registered
source theorem. -/
theorem quadraticC0_singularIntegral_eq_graph
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w) :
    singularIntegral (realQuadraticValue A) w =
      hbGraphIntegral (realQuadraticValue A) w (quadraticPositiveRoot A) :=
  quadraticC0_singularIntegral_eq_hbGraphIntegral A hA w a lam ha hlam hgeom
    (quadraticPositiveRoot_area_measure A)

/-- Absolute convergence of the actual surface integral is proved from
compact support and C₀ geometry after applying the general area formula. -/
theorem quadraticC0_singularIntegral_integrable_of_geometry
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (hw : IsSmoothWeight w)
    (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w) :
    IntegrableOn (fun x => w x / (‖gradient (realQuadraticValue A) x‖ : ℂ))
      {x : RealVector4 | realQuadraticValue A x = 0} euclideanSurfaceMeasure :=
  quadraticC0_singularIntegral_integrable A hA w hw a lam ha hlam hgeom
    (quadraticPositiveRoot_area_measure A)

/-- The registered source thin-slab limit converges to the actual
Euclidean surface integral for a controlled C₀ quadratic weight. -/
theorem quadraticC0_thinSlab_tendsto_singularIntegral
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (B : ℝ) (D : ℕ → ℝ) (a lam : ℝ)
    (hB : 0 < B) (hD : ∀ k, 0 < D k) (ha : 0 < a) (hlam : 0 < lam)
    (w : RealVector4 → ℂ)
    (hw : HBC0Control (realQuadraticValue A) B D a lam w) :
    Filter.Tendsto (thinSlabIntegral (realQuadraticValue A) w)
      (𝓝[>] (0 : ℝ)) (𝓝 (singularIntegral (realQuadraticValue A) w)) := by
  have hselector := quadraticPositiveRoot_hbGraphSelector A hA w a lam hlam hw.2
  have hlimit := (Trusted.heathBrown_singular_graph A B D a lam hB hD ha hlam w hw
    (quadraticPositiveRoot A) hselector).2
  rwa [← quadraticC0_singularIntegral_eq_graph A hA w a lam ha hlam hw.2] at hlimit

/-- The limiting functional used by the registered analytic estimates
equals the actual surface integral, rather than defining a replacement
for that integral. -/
theorem quadraticC0_thinSlabSingularIntegral_eq_singularIntegral
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (B : ℝ) (D : ℕ → ℝ) (a lam : ℝ)
    (hB : 0 < B) (hD : ∀ k, 0 < D k) (ha : 0 < a) (hlam : 0 < lam)
    (w : RealVector4 → ℂ)
    (hw : HBC0Control (realQuadraticValue A) B D a lam w) :
    thinSlabSingularIntegral (realQuadraticValue A) w =
      singularIntegral (realQuadraticValue A) w :=
  (quadraticC0_thinSlab_tendsto_singularIntegral A hA B D a lam hB hD ha hlam w hw).limUnder_eq

/-- Replacing a normalization functional by an equal one on the stated
family preserves every estimate and its original common constants. -/
theorem DeltaIntegralBounds.congr_sigma
    {F : RealVector4 → ℝ} {sigma tau : (RealVector4 → ℂ) → ℂ}
    {weights : Set (RealVector4 → ℂ)} {scales : Set ℝ}
    (h : DeltaIntegralBounds F sigma weights scales)
    (heq : ∀ w ∈ weights, sigma w = tau w) :
    DeltaIntegralBounds F tau weights scales where
  differentiable := h.differentiable
  zero_error := by
    intro j hj
    obtain ⟨C, hC, hbound⟩ := h.zero_error j hj
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    rw [← heq w hw]
    exact hbound w hw r hr
  zero_derivative := h.zero_derivative
  rapid := h.rapid
  decay := h.decay

/-- All uniform delta-integral conclusions on any scale set transfer
from the source limiting value to the actual surface integral throughout
an explicitly controlled C₀ family. -/
theorem DeltaIntegralBounds.quadraticC0_surface
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (B : ℝ) (D : ℕ → ℝ) (a lam : ℝ)
    (hB : 0 < B) (hD : ∀ k, 0 < D k) (ha : 0 < a) (hlam : 0 < lam)
    {weights : Set (RealVector4 → ℂ)} {scales : Set ℝ}
    (hweights : ∀ w ∈ weights, HBC0Control (realQuadraticValue A) B D a lam w)
    (h : DeltaIntegralBounds (realQuadraticValue A)
      (thinSlabSingularIntegral (realQuadraticValue A)) weights scales) :
    DeltaIntegralBounds (realQuadraticValue A)
      (singularIntegral (realQuadraticValue A)) weights scales :=
  h.congr_sigma (fun w hw =>
    quadraticC0_thinSlabSingularIntegral_eq_singularIntegral A hA B D a lam
      hB hD ha hlam w (hweights w hw))

end QuaternaryQuadraticForms
