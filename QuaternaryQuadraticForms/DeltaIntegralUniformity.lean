import QuaternaryQuadraticForms.DeltaIntegralBounds
import QuaternaryQuadraticForms.SurfaceIntegralTransport
import Mathlib.Tactic.Positivity

/-!
# Internal extension and finite coordinate transport of delta-integral bounds

The cutoff extension uses the estimate at the endpoint to retain the same
zero-frequency error constant.  A finite cover supplies common constants
before any weight is selected.  Orthogonal transport uses the actual
integral, its fixed-frequency derivative, and the actual surface integral.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

namespace DeltaIntegralBounds

/-- Vanishing of the actual integral and its derivative above a cutoff
extends all simultaneous estimates to every positive scale. -/
theorem extend_of_cutoff
    {F : RealVector4 → ℝ} {sigma : (RealVector4 → ℂ) → ℂ}
    {weights : Set (RealVector4 → ℂ)} {R : ℝ} (hR : 1 ≤ R)
    (h : DeltaIntegralBounds F sigma weights (Set.Ioc 0 R))
    (hzero : ∀ w ∈ weights, ∀ r, R ≤ r → ∀ v : RealVector4,
      deltaIntegral F w r v = 0)
    (hderiv : ∀ w ∈ weights, ∀ r, R ≤ r → ∀ v : RealVector4,
      HasDerivAt (fun t => deltaIntegral F w t v) 0 r) :
    DeltaIntegralBounds F sigma weights (Set.Ioi 0) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw r hr v
    by_cases hrR : r ≤ R
    · exact h.differentiable w hw r ⟨hr, hrR⟩ v
    · exact (hderiv w hw r (le_of_not_ge hrR) v).differentiableAt
  · intro j hj
    obtain ⟨C, hC, hbound⟩ := h.zero_error j hj
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    by_cases hrR : r ≤ R
    · exact hbound w hw r ⟨hr, hrR⟩
    · have hRr : R ≤ r := le_of_not_ge hrR
      have hb := hbound w hw R ⟨hRpos, le_rfl⟩
      rw [hzero w hw R le_rfl 0, zero_sub, norm_neg] at hb
      rw [hzero w hw r hRr 0, zero_sub, norm_neg]
      exact hb.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hRpos.le hRr j) hC.le)
  · obtain ⟨C, hC, hbound⟩ := h.zero_derivative
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    by_cases hrR : r ≤ R
    · exact hbound w hw r ⟨hr, hrR⟩
    · rw [(hderiv w hw r (le_of_not_ge hrR) 0).deriv, norm_zero]
      exact mul_nonneg hC.le (inv_nonneg.mpr (le_of_lt hr))
  · intro j hj
    obtain ⟨C, hC, hbound⟩ := h.rapid j hj
    refine ⟨C, hC, ?_⟩
    intro w hw r hr v hv
    by_cases hrR : r ≤ R
    · exact hbound w hw r ⟨hr, hrR⟩ v hv
    · rw [hzero w hw r (le_of_not_ge hrR) v, norm_zero]
      exact mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr (le_of_lt hr)))
        (pow_nonneg (inv_nonneg.mpr (norm_nonneg v)) j)
  · intro ε hε hεhalf
    obtain ⟨C, hC, hbound⟩ := h.decay ε hε hεhalf
    refine ⟨C, hC, ?_⟩
    intro w hw r hr v hv
    by_cases hrR : r ≤ R
    · exact hbound w hw r ⟨hr, hrR⟩ v hv
    · rw [hzero w hw r (le_of_not_ge hrR) v,
        (hderiv w hw r (le_of_not_ge hrR) v).deriv, norm_zero, mul_zero, add_zero]
      exact mul_nonneg
        (mul_nonneg hC.le (Real.rpow_nonneg (le_of_lt hr) _))
        (Real.rpow_nonneg (norm_nonneg v) _)

private theorem positive_finite_majorant {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, c i ≤ C := by
  classical
  refine ⟨1 + ∑ i, c i, ?_, ?_⟩
  · have hs : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    linarith
  · intro i
    have hi : c i ≤ ∑ k, c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    linarith

/-- Finitely many subfamilies have common positive constants on positive
scales. No nonemptiness assumption on the index or weight families is needed. -/
theorem of_finite_cover
    {ι : Type*} [Fintype ι]
    {F : RealVector4 → ℝ} {sigma : (RealVector4 → ℂ) → ℂ}
    {weights : Set (RealVector4 → ℂ)} {scales : Set ℝ}
    (families : ι → Set (RealVector4 → ℂ))
    (hscales : scales ⊆ Set.Ioi 0)
    (hcover : ∀ w ∈ weights, ∃ i, w ∈ families i)
    (h : ∀ i, DeltaIntegralBounds F sigma (families i) scales) :
    DeltaIntegralBounds F sigma weights scales := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw r hr v
    obtain ⟨i, hwi⟩ := hcover w hw
    exact (h i).differentiable w hwi r hr v
  · intro j hj
    choose c hc hbound using (fun i => (h i).zero_error j hj)
    obtain ⟨C, hC, hcC⟩ := positive_finite_majorant c hc
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    obtain ⟨i, hwi⟩ := hcover w hw
    exact (hbound i w hwi r hr).trans (mul_le_mul_of_nonneg_right (hcC i)
      (pow_nonneg (le_of_lt (hscales hr)) j))
  · choose c hc hbound using (fun i => (h i).zero_derivative)
    obtain ⟨C, hC, hcC⟩ := positive_finite_majorant c hc
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    obtain ⟨i, hwi⟩ := hcover w hw
    exact (hbound i w hwi r hr).trans (mul_le_mul_of_nonneg_right (hcC i)
      (inv_nonneg.mpr (le_of_lt (hscales hr))))
  · intro j hj
    choose c hc hbound using (fun i => (h i).rapid j hj)
    obtain ⟨C, hC, hcC⟩ := positive_finite_majorant c hc
    refine ⟨C, hC, ?_⟩
    intro w hw r hr v hv
    obtain ⟨i, hwi⟩ := hcover w hw
    exact (hbound i w hwi r hr v hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcC i) (inv_nonneg.mpr (le_of_lt (hscales hr))))
        (pow_nonneg (inv_nonneg.mpr (norm_nonneg v)) j))
  · intro ε hε hεhalf
    choose c hc hbound using (fun i => (h i).decay ε hε hεhalf)
    obtain ⟨C, hC, hcC⟩ := positive_finite_majorant c hc
    refine ⟨C, hC, ?_⟩
    intro w hw r hr v hv
    obtain ⟨i, hwi⟩ := hcover w hw
    exact (hbound i w hwi r hr v hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcC i)
          (Real.rpow_nonneg (le_of_lt (hscales hr)) _))
        (Real.rpow_nonneg (norm_nonneg v) _))

/-- Transport from one orthogonal coordinate system preserves every
constant, including both fixed-frequency derivative estimates. -/
theorem of_realIsometry
    {F : RealVector4 → ℝ} (hF : Differentiable ℝ F)
    {weights transformed : Set (RealVector4 → ℂ)} {scales : Set ℝ}
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4)
    (hcover : ∀ w ∈ weights, (fun x => w (e x)) ∈ transformed)
    (h : DeltaIntegralBounds (fun x => F (e x))
      (singularIntegral (fun x => F (e x))) transformed scales) :
    DeltaIntegralBounds F (singularIntegral F) weights scales := by
  have hfun (w : RealVector4 → ℂ) (v : RealVector4) :
      (fun t => deltaIntegral (fun x => F (e x)) (fun x => w (e x)) t (e.symm v)) =
        (fun t => deltaIntegral F w t v) := by
    funext t
    exact deltaIntegral_comp_realIsometry F w t v e
  have hfun0 (w : RealVector4 → ℂ) :
      (fun t => deltaIntegral (fun x => F (e x)) (fun x => w (e x)) t 0) =
        (fun t => deltaIntegral F w t 0) := by
    simpa only [map_zero] using hfun w 0
  have hval0 (w : RealVector4 → ℂ) (r : ℝ) :
      deltaIntegral (fun x => F (e x)) (fun x => w (e x)) r 0 = deltaIntegral F w r 0 :=
    congrFun (hfun0 w) r
  have hnv (v : RealVector4) (hv : v ≠ 0) : e.symm v ≠ 0 := by
    intro hz
    apply hv
    simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw r hr v
    simpa only [hfun w v] using h.differentiable (fun x => w (e x)) (hcover w hw)
      r hr (e.symm v)
  · intro j hj
    obtain ⟨C, hC, hbound⟩ := h.zero_error j hj
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    simpa only [hval0 w r, singularIntegral_comp_realIsometry F hF w e] using
      hbound (fun x => w (e x)) (hcover w hw) r hr
  · obtain ⟨C, hC, hbound⟩ := h.zero_derivative
    refine ⟨C, hC, ?_⟩
    intro w hw r hr
    simpa only [hfun0 w] using hbound (fun x => w (e x)) (hcover w hw) r hr
  · intro j hj
    obtain ⟨C, hC, hbound⟩ := h.rapid j hj
    refine ⟨C, hC, ?_⟩
    intro w hw r hr v hv
    simpa only [deltaIntegral_comp_realIsometry F w r v e, e.symm.norm_map] using
      hbound (fun x => w (e x)) (hcover w hw) r hr (e.symm v) (hnv v hv)
  · intro ε hε hεhalf
    obtain ⟨C, hC, hbound⟩ := h.decay ε hε hεhalf
    refine ⟨C, hC, ?_⟩
    intro w hw r hr v hv
    simpa only [deltaIntegral_comp_realIsometry F w r v e, hfun w v, e.symm.norm_map] using
      hbound (fun x => w (e x)) (hcover w hw) r hr (e.symm v) (hnv v hv)

/-- A finite choice of signed coordinate systems can be made separately
for every weight while retaining constants uniform over the original family. -/
theorem of_isometry_cover
    {F : RealVector4 → ℝ} (hF : Differentiable ℝ F)
    {weights : Set (RealVector4 → ℂ)} {scales : Set ℝ}
    (families : SignedCoordinateChange → Set (RealVector4 → ℂ))
    (hscales : scales ⊆ Set.Ioi 0)
    (hcover : ∀ w ∈ weights, ∃ s : SignedCoordinateChange,
      (fun x => w (signedCoordinateIsometry s x)) ∈ families s)
    (h : ∀ s : SignedCoordinateChange,
      DeltaIntegralBounds (fun x => F (signedCoordinateIsometry s x))
        (singularIntegral (fun x => F (signedCoordinateIsometry s x))) (families s) scales) :
    DeltaIntegralBounds F (singularIntegral F) weights scales := by
  apply of_finite_cover
    (fun s : SignedCoordinateChange =>
      {w | (fun x => w (signedCoordinateIsometry s x)) ∈ families s}) hscales hcover
  intro s
  exact of_realIsometry hF (signedCoordinateIsometry s) (fun _ hw => hw) (h s)

end DeltaIntegralBounds

end QuaternaryQuadraticForms
