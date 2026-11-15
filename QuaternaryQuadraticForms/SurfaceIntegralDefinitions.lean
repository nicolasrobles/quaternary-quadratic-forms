import QuaternaryQuadraticForms.AnalyticDefinitions
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The actual surface measure and singular integral

Mathlib's Hausdorff measure uses powers of diameters without the Euclidean
normalization. Multiplication by the volume of the three-dimensional unit
ball divided by `2^3` gives the usual Euclidean surface measure. This is
the normalization in the cited general area formula, not a choice of a
delta-method limiting functional.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped Topology ENNReal

/-- The conventional normalized three-dimensional Hausdorff measure in
Euclidean four-space. The normalization is `vol(B^3_1)/2^3`. -/
def euclideanSurfaceMeasure : Measure RealVector4 :=
  (volume (Metric.ball (0 : RealVector3) 1) / (2 : ℝ≥0∞) ^ 3) •
    (Measure.hausdorffMeasure 3 : Measure RealVector4)

/-- The literal surface integral from equation (1.3), with the actual
Euclidean gradient in its denominator. -/
def singularIntegral (F : RealVector4 → ℝ) (w : RealVector4 → ℂ) : ℂ :=
  ∫ x in {x : RealVector4 | F x = 0},
    w x / (‖gradient F x‖ : ℂ) ∂euclideanSurfaceMeasure

/-- The actual graph map, with its distinguished coordinate first. -/
def surfaceGraph (φ : RealVector3 → ℝ) (y : RealVector3) : RealVector4 :=
  graphPoint (φ y) y

/-- The Euclidean graph area factor, for the cited general area formula. -/
def graphAreaFactor (φ : RealVector3 → ℝ) (y : RealVector3) : ℝ :=
  Real.sqrt (1 + ‖gradient φ y‖ ^ 2)

/-- The actual thin-slab expression used in Heath--Brown's Theorem 3. -/
def thinSlabIntegral (F : RealVector4 → ℝ) (w : RealVector4 → ℂ)
    (ε : ℝ) : ℂ :=
  ((2 * ε : ℝ) : ℂ)⁻¹ * ∫ x in {x : RealVector4 | |F x| ≤ ε}, w x

/-- The source limiting value. Its existence and equality with the actual
surface integral are separate assertions, never definitional substitutions. -/
def thinSlabSingularIntegral (F : RealVector4 → ℝ)
    (w : RealVector4 → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (thinSlabIntegral F w)

end QuaternaryQuadraticForms
