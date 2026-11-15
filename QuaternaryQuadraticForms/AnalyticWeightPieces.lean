import QuaternaryQuadraticForms.AnalyticWeightBump
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual localized source weights

The pieces use the fixed product bump with no absorbed scale factor.
Their support and Euclidean radius, smoothness, and exact reconstruction
are proved from the actual definitions and Lebesgue change of variables.
The original weights may be complex-valued.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped ContDiff

private instance realVector4_volume_isNegInvariant :
    Measure.IsNegInvariant (volume : Measure RealVector4) where
  neg_eq_self := (LinearIsometryEquiv.neg ℝ (E := RealVector4)).measurePreserving.map_eq

/-- Localization preserves smoothness for every fixed scale and centre. -/
theorem localizedWeight_contDiff (W : RealVector4 → ℂ)
    (hW : ContDiff ℝ ∞ W) (δ : ℝ) (y : RealVector4) :
    ContDiff ℝ ∞ (localizedWeight W δ y) := by
  unfold localizedWeight
  apply hW.mul
  exact Complex.ofRealCLM.contDiff.comp
    (heathBrownTheta_contDiff.comp (contDiff_const.smul (contDiff_id.sub contDiff_const)))

/-- The closed support of each piece is contained in the original closed
support. No regularity of the original weight is needed for this fact. -/
theorem localizedWeight_tsupport_subset (W : RealVector4 → ℂ)
    (δ : ℝ) (y : RealVector4) :
    tsupport (localizedWeight W δ y) ⊆ tsupport W :=
  tsupport_mul_subset_left

/-- The source coordinate cube gives the precise Euclidean radius `2δ`
for every four-dimensional piece. -/
theorem localizedWeight_tsupport_subset_closedBall (W : RealVector4 → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (y : RealVector4) :
    tsupport (localizedWeight W δ y) ⊆ Metric.closedBall y (2 * δ) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have htheta : heathBrownTheta (δ⁻¹ • (x - y)) ≠ 0 := by
    intro hz
    exact hx (by simp [localizedWeight, hz])
  have hb := heathBrownTheta_norm_le_two_of_mem_tsupport (δ⁻¹ • (x - y))
    (subset_tsupport heathBrownTheta htheta)
  have hnorm : ‖x - y‖ / δ ≤ 2 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ,
      div_eq_mul_inv, mul_comm] using hb
  simpa only [Metric.mem_closedBall, dist_eq_norm] using (div_le_iff₀ hδ).mp hnorm

/-- Each positive-scale piece has compact support, even before any
compactness assumption is imposed on its original weight. -/
theorem localizedWeight_hasCompactSupport (W : RealVector4 → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (y : RealVector4) :
    HasCompactSupport (localizedWeight W δ y) :=
  (isCompact_closedBall y (2 * δ)).of_isClosed_subset
    (isClosed_tsupport _) (localizedWeight_tsupport_subset_closedBall W δ hδ y)

/-- The source localized functions are actual smooth compactly supported
weights. -/
theorem localizedWeight_isSmoothWeight (W : RealVector4 → ℂ)
    (hW : IsSmoothWeight W) (δ : ℝ) (hδ : 0 < δ) (y : RealVector4) :
    IsSmoothWeight (localizedWeight W δ y) :=
  ⟨localizedWeight_contDiff W hW.1 δ y,
    localizedWeight_hasCompactSupport W δ hδ y⟩

/-- A nonzero piece has its centre within distance `2δ` of an actual
point of the original support. -/
theorem localizedWeight_nonzero_imp_near_support (W : RealVector4 → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (y : RealVector4)
    (hne : localizedWeight W δ y ≠ 0) :
    ∃ x ∈ tsupport W, dist y x ≤ 2 * δ := by
  classical
  have hex : ∃ x : RealVector4, localizedWeight W δ y x ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨x, hx⟩ := hex
  have hxs : x ∈ tsupport (localizedWeight W δ y) := subset_tsupport _ hx
  refine ⟨x, localizedWeight_tsupport_subset W δ y hxs, ?_⟩
  have hdist := localizedWeight_tsupport_subset_closedBall W δ hδ y hxs
  simpa only [Metric.mem_closedBall, dist_comm] using hdist

/-- Translation, reflection and scaling give the exact normalization of
the bump when integrating over its centre. -/
theorem heathBrownTheta_integral_scaled_translate (δ : ℝ) (hδ : 0 < δ)
    (x : RealVector4) :
    (∫ y : RealVector4, heathBrownTheta (δ⁻¹ • (x - y))) = δ ^ 4 := by
  calc
    _ = ∫ y : RealVector4, heathBrownTheta (δ⁻¹ • y) :=
      integral_sub_left_eq_self (fun y : RealVector4 => heathBrownTheta (δ⁻¹ • y)) volume x
    _ = δ ^ 4 * ∫ y : RealVector4, heathBrownTheta y := by
      simpa only [RealVector4, finrank_euclideanSpace_fin, smul_eq_mul] using
        Measure.integral_comp_inv_smul_of_nonneg volume heathBrownTheta hδ.le
    _ = δ ^ 4 := by rw [heathBrownTheta_integral, mul_one]

/-- For each fixed source point, the pieces are integrable as a function
of their centre. -/
theorem localizedWeight_integrable_in_center (W : RealVector4 → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (x : RealVector4) :
    Integrable (fun y : RealVector4 => localizedWeight W δ y x) := by
  have hb : Integrable (fun y : RealVector4 => heathBrownTheta (δ⁻¹ • (x - y))) :=
    (heathBrownTheta_integrable.comp_smul (inv_ne_zero hδ.ne')).comp_sub_left x
  exact (Complex.ofRealCLM.integrable_comp hb).const_mul (W x)

/-- The unnormalized centre integral is exactly `δ^4 W(x)`. -/
theorem localizedWeight_integral_center (W : RealVector4 → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (x : RealVector4) :
    (∫ y : RealVector4, localizedWeight W δ y x) = (δ ^ 4 : ℝ) • W x := by
  simp only [localizedWeight]
  rw [integral_const_mul, integral_complex_ofReal,
    heathBrownTheta_integral_scaled_translate δ hδ x, Complex.real_smul, mul_comm]

/-- The exact reconstruction formula of equation (2.3), with its source
factor `δ⁻⁴` and the original complex weight. -/
theorem localizedWeight_reconstruction (W : RealVector4 → ℂ)
    (δ : ℝ) (hδ : 0 < δ) (x : RealVector4) :
    (δ⁻¹ ^ 4 : ℝ) • (∫ y : RealVector4, localizedWeight W δ y x) = W x := by
  rw [localizedWeight_integral_center W δ hδ x, smul_smul, ← mul_pow,
    inv_mul_cancel₀ hδ.ne', one_pow, one_smul]

end QuaternaryQuadraticForms
