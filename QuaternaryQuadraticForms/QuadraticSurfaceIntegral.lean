import QuaternaryQuadraticForms.SurfaceGraphIntegral
import QuaternaryQuadraticForms.QuadraticPositiveRootChart
import QuaternaryQuadraticForms.HeathBrownIntegralDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual quadratic surface integral and Heath--Brown's graph integral

The C₀ interval geometry selects the explicit positive-coordinate root
of the quadratic form. Its projected support lies in that root's open
domain. The other zero-set branches contribute zero because the weight
vanishes there. The Euclidean graph area factor then cancels against the
actual gradient norm.

The general area measure identity is an explicit hypothesis in this
module. Every deduction specific to the quadratic form and localized
source weight, including absolute integrability, is proved internally.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped ContDiff

/-- The source support projection is the actual continuous coordinate
projection of Euclidean space. -/
theorem realVectorTail_continuous : Continuous realVectorTail :=
  graphTail_continuous

/-- Taking the tail of a graph insertion recovers its three parameters. -/
@[simp] theorem realVectorTail_graphPoint (t : ℝ) (y : RealVector3) :
    realVectorTail (graphPoint t y) = y :=
  graphTail_graphPoint t y

/-- The source tail projection and first coordinate reconstruct every
actual four-vector. -/
theorem graphPoint_realVectorTail (x : RealVector4) :
    graphPoint (x 0) (realVectorTail x) = x :=
  graphPoint_graphTail x

/-- The parameters of the actual graph are recovered by source projection. -/
@[simp] theorem realVectorTail_surfaceGraph (φ : RealVector3 → ℝ) (y : RealVector3) :
    realVectorTail (surfaceGraph φ y) = y :=
  realVectorTail_graphPoint (φ y) y

/-- The source's projected closed support is compact for a compactly
supported weight. -/
theorem weightTailSupport_isCompact (w : RealVector4 → ℂ)
    (hw : HasCompactSupport w) : IsCompact (weightTailSupport w) :=
  hw.image realVectorTail_continuous

private theorem quadraticC0_root_data
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w)
    (x : RealVector4) (hx : x ∈ tsupport w) :
    realVectorTail x ∈ quadraticPositiveRootDomain A ∧
      |quadraticPositiveRoot A (realVectorTail x) - x 0| ≤ a ∧
      realQuadraticValue A
        (surfaceGraph (quadraticPositiveRoot A) (realVectorTail x)) = 0 := by
  obtain ⟨t, ht, _⟩ := hgeom.2 x hx
  have hpos : 0 < gradient (realQuadraticValue A)
      (graphPoint t (realVectorTail x)) 0 :=
    lt_of_lt_of_le hlam (hgeom.1 x hx t ht.1)
  have hroot := quadraticPositiveRoot_unique A hA t (realVectorTail x) ht.2 hpos
  refine ⟨hroot.1, ?_, ?_⟩
  · simpa only [← hroot.2] using ht.1
  · simpa only [surfaceGraph, ← hroot.2] using ht.2

/-- The root selected independently by the source intervals is the
single explicit positive-coordinate root of the actual quadratic form. -/
theorem quadraticPositiveRoot_hbGraphSelector
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w) :
    HBGraphSelector (realQuadraticValue A) w a (quadraticPositiveRoot A) := by
  intro x hx
  exact (quadraticC0_root_data A hA w a lam hlam hgeom x hx).2

/-- Every projected point of the actual closed support lies inside the
open smooth domain of the explicit quadratic chart. -/
theorem weightTailSupport_subset_quadraticPositiveRootDomain
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w) :
    weightTailSupport w ⊆ quadraticPositiveRootDomain A := by
  rintro y ⟨x, hx, rfl⟩
  exact (quadraticC0_root_data A hA w a lam hlam hgeom x hx).1

/-- The source interval derivative lower bound holds in particular at
the original support point. -/
theorem quadraticC0_gradient_zero_pos_on_tsupport
    (A : Matrix (Fin 4) (Fin 4) ℝ) (w : RealVector4 → ℂ)
    (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w)
    (x : RealVector4) (hx : x ∈ tsupport w) :
    0 < gradient (realQuadraticValue A) x 0 := by
  have h := hgeom.1 x hx (x 0) (by simpa only [sub_self, abs_zero] using ha.le)
  rw [graphPoint_realVectorTail] at h
  exact lt_of_lt_of_le hlam h

/-- Every actual zero in the support of a C₀ weight belongs to the
positive-coordinate graph branch. -/
theorem quadraticC0_zero_mem_graph_of_mem_tsupport
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w)
    (x : RealVector4) (hx : x ∈ tsupport w) (hzero : realQuadraticValue A x = 0) :
    x ∈ surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A := by
  have hpos := quadraticC0_gradient_zero_pos_on_tsupport A w a lam ha hlam hgeom x hx
  have hroot := quadraticPositiveRoot_unique A hA (x 0) (realVectorTail x)
    (by simpa only [graphPoint_realVectorTail] using hzero)
    (by simpa only [graphPoint_realVectorTail] using hpos)
  refine ⟨realVectorTail x, hroot.1, ?_⟩
  rw [surfaceGraph, ← hroot.2, graphPoint_realVectorTail]

private theorem quadraticC0_weight_zero_off_graph
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w)
    (x : RealVector4) (hzero : realQuadraticValue A x = 0)
    (hx : x ∉ surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A) :
    w x = 0 := by
  by_contra hne
  exact hx (quadraticC0_zero_mem_graph_of_mem_tsupport A hA w a lam ha hlam hgeom x
    (subset_tsupport w hne) hzero)

/-- The graph numerator vanishes outside the source projected support,
for every graph function. -/
theorem weight_surfaceGraph_eq_zero_of_notMem_tailSupport
    (w : RealVector4 → ℂ) (φ : RealVector3 → ℝ) (y : RealVector3)
    (hy : y ∉ weightTailSupport w) : w (surfaceGraph φ y) = 0 := by
  by_contra hne
  exact hy ⟨surfaceGraph φ y, subset_tsupport w hne, realVectorTail_surfaceGraph φ y⟩

/-- The actual Euclidean surface Jacobian cancels against the full
gradient denominator, leaving the positive first coordinate derivative. -/
theorem quadraticPositiveRoot_area_div_gradient
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (y : RealVector3)
    (hy : y ∈ quadraticPositiveRootDomain A) :
    graphAreaFactor (quadraticPositiveRoot A) y •
      (w (surfaceGraph (quadraticPositiveRoot A) y) /
        (‖gradient (realQuadraticValue A)
          (surfaceGraph (quadraticPositiveRoot A) y)‖ : ℂ)) =
      w (surfaceGraph (quadraticPositiveRoot A) y) /
        (gradient (realQuadraticValue A)
          (surfaceGraph (quadraticPositiveRoot A) y) 0 : ℂ) := by
  rw [quadraticPositiveRoot_gradient_norm A hA y hy, Complex.ofReal_mul,
    Complex.real_smul]
  have harea : (graphAreaFactor (quadraticPositiveRoot A) y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (graphAreaFactor_pos _ _).ne'
  have hcoord : (gradient (realQuadraticValue A)
      (surfaceGraph (quadraticPositiveRoot A) y) 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (quadraticPositiveRoot_gradient_zero_pos A hA y hy).ne'
  field_simp

/-- The graph integrand is continuous on its actual open chart domain.
Only the original weight is globally smooth; the root is used locally. -/
theorem quadraticPositiveRoot_graphIntegrand_continuousOn
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (hw : Continuous w) :
    ContinuousOn
      (fun y => w (surfaceGraph (quadraticPositiveRoot A) y) /
        (gradient (realQuadraticValue A)
          (surfaceGraph (quadraticPositiveRoot A) y) 0 : ℂ))
      (quadraticPositiveRootDomain A) := by
  have hgraph : ContinuousOn (surfaceGraph (quadraticPositiveRoot A))
      (quadraticPositiveRootDomain A) :=
    graphPoint_continuous.comp_continuousOn
      ((quadraticPositiveRoot_contDiffOn A).continuousOn.prodMk continuous_id.continuousOn)
  have hg : Continuous (fun x : RealVector4 => gradient (realQuadraticValue A) x 0) := by
    simp only [gradient_realQuadraticValue A hA]
    exact (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).comp
      (realQuadraticGradient_continuous A)
  exact (hw.comp_continuousOn hgraph).div
    (Complex.continuous_ofReal.comp_continuousOn (hg.comp_continuousOn hgraph))
    (fun y hy => Complex.ofReal_ne_zero.mpr
      (quadraticPositiveRoot_gradient_zero_pos A hA y hy).ne')

/-- The literal Heath--Brown graph integrand is integrable. Compactness
of the actual projected support and continuity on the open chart prove
convergence; this is not a default Bochner integral value. -/
theorem quadraticPositiveRoot_graphIntegrand_integrable
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (hw : IsSmoothWeight w)
    (a lam : ℝ) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w) :
    Integrable (fun y => w (surfaceGraph (quadraticPositiveRoot A) y) /
      (gradient (realQuadraticValue A)
        (surfaceGraph (quadraticPositiveRoot A) y) 0 : ℂ)) := by
  have hsub := weightTailSupport_subset_quadraticPositiveRootDomain A hA w a lam hlam hgeom
  have hc := (quadraticPositiveRoot_graphIntegrand_continuousOn A hA w hw.1.continuous).mono hsub
  have hi := hc.integrableOn_compact (μ := volume) (weightTailSupport_isCompact w hw.2)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro y hy
  rw [weight_surfaceGraph_eq_zero_of_notMem_tailSupport w _ y hy, zero_div]

/-- Identification of the actual normalized Hausdorff surface integral
with the source graph expression. The sole external geometric input is
the explicit general area measure identity. -/
theorem quadraticC0_singularIntegral_eq_hbGraphIntegral
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w)
    (harea : euclideanSurfaceMeasure.restrict
        (surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A) =
      Measure.map (surfaceGraph (quadraticPositiveRoot A))
        ((volume.restrict (quadraticPositiveRootDomain A)).withDensity
          (fun y => ENNReal.ofReal (graphAreaFactor (quadraticPositiveRoot A) y)))) :
    singularIntegral (realQuadraticValue A) w =
      hbGraphIntegral (realQuadraticValue A) w (quadraticPositiveRoot A) := by
  have hzero : MeasurableSet {x : RealVector4 | realQuadraticValue A x = 0} :=
    isClosed_eq (realQuadraticValue_continuous A) continuous_const |>.measurableSet
  have hU := (quadraticPositiveRootDomain_isOpen A).measurableSet
  have hgraphsub : surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A ⊆
      {x : RealVector4 | realQuadraticValue A x = 0} := by
    rintro x ⟨y, hy, rfl⟩
    exact quadraticPositiveRoot_value_zero A hA y hy
  unfold singularIntegral hbGraphIntegral
  calc
    _ = ∫ x in surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A,
        w x / (‖gradient (realQuadraticValue A) x‖ : ℂ) ∂euclideanSurfaceMeasure := by
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hzero hgraphsub
      intro x hx
      rw [quadraticC0_weight_zero_off_graph A hA w a lam ha hlam hgeom x hx.1 hx.2,
        zero_div]
    _ = ∫ y in quadraticPositiveRootDomain A,
        graphAreaFactor (quadraticPositiveRoot A) y •
          (w (surfaceGraph (quadraticPositiveRoot A) y) /
            (‖gradient (realQuadraticValue A)
              (surfaceGraph (quadraticPositiveRoot A) y)‖ : ℂ)) :=
      integral_surfaceGraph_image _ (quadraticPositiveRoot_measurable A) _ harea _
    _ = ∫ y in quadraticPositiveRootDomain A,
        w (surfaceGraph (quadraticPositiveRoot A) y) /
          (gradient (realQuadraticValue A)
            (surfaceGraph (quadraticPositiveRoot A) y) 0 : ℂ) := by
      apply setIntegral_congr_fun hU
      intro y hy
      exact quadraticPositiveRoot_area_div_gradient A hA w y hy
    _ = _ := by
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hU
        (weightTailSupport_subset_quadraticPositiveRootDomain A hA w a lam hlam hgeom)
      intro y hy
      rw [weight_surfaceGraph_eq_zero_of_notMem_tailSupport w _ y hy.2, zero_div]

/-- The actual surface-integral integrand is absolutely integrable for
a smooth compact C₀ quadratic weight. -/
theorem quadraticC0_singularIntegral_integrable
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A)
    (w : RealVector4 → ℂ) (hw : IsSmoothWeight w)
    (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hgeom : HBC0Geometry (realQuadraticValue A) a lam w)
    (harea : euclideanSurfaceMeasure.restrict
        (surfaceGraph (quadraticPositiveRoot A) '' quadraticPositiveRootDomain A) =
      Measure.map (surfaceGraph (quadraticPositiveRoot A))
        ((volume.restrict (quadraticPositiveRootDomain A)).withDensity
          (fun y => ENNReal.ofReal (graphAreaFactor (quadraticPositiveRoot A) y)))) :
    IntegrableOn (fun x => w x / (‖gradient (realQuadraticValue A) x‖ : ℂ))
      {x : RealVector4 | realQuadraticValue A x = 0} euclideanSurfaceMeasure := by
  have hU := (quadraticPositiveRootDomain_isOpen A).measurableSet
  have hJ := quadraticPositiveRoot_graphIntegrand_integrable A hA w hw a lam hlam hgeom
  have hweighted : IntegrableOn
      (fun y => graphAreaFactor (quadraticPositiveRoot A) y •
        (w (surfaceGraph (quadraticPositiveRoot A) y) /
          (‖gradient (realQuadraticValue A)
            (surfaceGraph (quadraticPositiveRoot A) y)‖ : ℂ)))
      (quadraticPositiveRootDomain A) :=
    (integrableOn_congr_fun
      (fun y hy => quadraticPositiveRoot_area_div_gradient A hA w y hy) hU).mpr
      hJ.integrableOn
  have hi := (integrable_surfaceGraph_image_iff _ (quadraticPositiveRoot_measurable A) _
    harea (fun x => w x / (‖gradient (realQuadraticValue A) x‖ : ℂ))).mpr hweighted
  apply hi.of_forall_diff_eq_zero
    (isClosed_eq (realQuadraticValue_continuous A) continuous_const |>.measurableSet)
  intro x hx
  rw [quadraticC0_weight_zero_off_graph A hA w a lam ha hlam hgeom x hx.1 hx.2, zero_div]

end QuaternaryQuadraticForms
