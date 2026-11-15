import QuaternaryQuadraticForms.SurfaceIntegralDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integration on a graph from an explicit area measure identity

This module proves the complex Bochner integration and integrability
consequences of the general graph area formula. The area measure
identity remains an explicit hypothesis here; no literature premise is
introduced. Its eventual cited wrapper supplies differentiability only
on its open graph domain. None of these deductions requires a globally
smooth extension of the graph function.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory

/-- The graph map is injective because its last three coordinates are
the original point. -/
theorem surfaceGraph_injective (φ : RealVector3 → ℝ) :
    Function.Injective (surfaceGraph φ) := by
  intro y z h
  ext i
  have hi := congrArg (fun x : RealVector4 => x i.succ) h
  exact hi

/-- A measurable graph function gives a measurable actual Euclidean
graph map, without any global differentiability assumption. -/
theorem surfaceGraph_measurable (φ : RealVector3 → ℝ) (hφ : Measurable φ) :
    Measurable (surfaceGraph φ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hφ
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable

/-- The actual graph is a measurable embedding. This permits change of
variables for all complex integrands, including the integrability
equivalence, without an additional ambient measurability premise. -/
theorem surfaceGraph_measurableEmbedding (φ : RealVector3 → ℝ)
    (hφ : Measurable φ) : MeasurableEmbedding (surfaceGraph φ) :=
  (surfaceGraph_measurable φ hφ).measurableEmbedding (surfaceGraph_injective φ)

/-- The Euclidean graph area factor is strictly positive everywhere. -/
theorem graphAreaFactor_pos (φ : RealVector3 → ℝ) (y : RealVector3) :
    0 < graphAreaFactor φ y :=
  Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))

/-- Nonnegativity is available for the real-to-extended-real density. -/
theorem graphAreaFactor_nonneg (φ : RealVector3 → ℝ) (y : RealVector3) :
    0 ≤ graphAreaFactor φ y := (graphAreaFactor_pos φ y).le

/-- Mathlib's actual derivative is Borel measurable, so the area density
is measurable even when smoothness is available only on a graph domain. -/
theorem graphAreaFactor_measurable (φ : RealVector3 → ℝ) :
    Measurable (graphAreaFactor φ) := by
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ RealVector3).symm.continuous.measurable.comp
      (measurable_fderiv ℝ φ)
  exact (measurable_const.add (hg.norm.pow_const 2)).sqrt

/-- The complex integral over the actual graph surface equals the
Lebesgue graph integral, given the explicit general area measure identity. -/
theorem integral_surfaceGraph_image
    (φ : RealVector3 → ℝ) (hφ : Measurable φ) (U : Set RealVector3)
    (harea : euclideanSurfaceMeasure.restrict (surfaceGraph φ '' U) =
      Measure.map (surfaceGraph φ)
        ((volume.restrict U).withDensity
          (fun y => ENNReal.ofReal (graphAreaFactor φ y))))
    (g : RealVector4 → ℂ) :
    (∫ x in surfaceGraph φ '' U, g x ∂euclideanSurfaceMeasure) =
      ∫ y in U, graphAreaFactor φ y • g (surfaceGraph φ y) := by
  rw [harea, (surfaceGraph_measurableEmbedding φ hφ).integral_map]
  rw [integral_withDensity_eq_integral_toReal_smul
    (graphAreaFactor_measurable φ).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [ENNReal.toReal_ofReal (graphAreaFactor_nonneg φ y)])

/-- Absolute integrability on the actual graph surface is equivalent to
absolute integrability of the density-weighted graph integrand. -/
theorem integrable_surfaceGraph_image_iff
    (φ : RealVector3 → ℝ) (hφ : Measurable φ) (U : Set RealVector3)
    (harea : euclideanSurfaceMeasure.restrict (surfaceGraph φ '' U) =
      Measure.map (surfaceGraph φ)
        ((volume.restrict U).withDensity
          (fun y => ENNReal.ofReal (graphAreaFactor φ y))))
    (g : RealVector4 → ℂ) :
    IntegrableOn g (surfaceGraph φ '' U) euclideanSurfaceMeasure ↔
      IntegrableOn (fun y => graphAreaFactor φ y • g (surfaceGraph φ y)) U := by
  unfold IntegrableOn
  rw [harea, (surfaceGraph_measurableEmbedding φ hφ).integrable_map_iff]
  rw [integrable_withDensity_iff_integrable_smul'
    (graphAreaFactor_measurable φ).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (graphAreaFactor_nonneg φ _), Function.comp_def]

end QuaternaryQuadraticForms
