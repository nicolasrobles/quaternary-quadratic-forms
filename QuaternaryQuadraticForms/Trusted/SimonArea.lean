import QuaternaryQuadraticForms.SurfaceIntegralDefinitions

/-!
The separately registered general graph area formula from Simon. See certification/correspondence/surface_area_formula.md.
-/

noncomputable section

open QuaternaryQuadraticForms MeasureTheory
open scoped ContDiff Topology

axiom QuaternaryQuadraticForms.Trusted.simon_graph_area :
  ∀ (U : Set RealVector3) (φ : RealVector3 → ℝ),
    IsOpen U → Measurable φ → ContDiffOn ℝ 1 φ U →
      euclideanSurfaceMeasure.restrict (surfaceGraph φ '' U) =
        Measure.map (surfaceGraph φ)
          ((volume.restrict U).withDensity
            (fun y => ENNReal.ofReal (graphAreaFactor φ y)))
