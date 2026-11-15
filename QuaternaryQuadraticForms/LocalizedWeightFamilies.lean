import QuaternaryQuadraticForms.AnalyticWeightDerivativeBounds
import QuaternaryQuadraticForms.HeathBrownQuadraticHypotheses

/-!
# The common localized and transformed weight families

These definitions retain the actual W_y. Smoothness, support, and all
coordinate-partial bounds are proved uniformly before selecting W, y,
or any orthogonal coordinate change.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped ContDiff

/-- The full family of actual localized pieces at one fixed scale. -/
def localizedWeightFamily (weights : Set (RealVector4 → ℂ)) (δ : ℝ) :
    Set (RealVector4 → ℂ) :=
  {w | ∃ W ∈ weights, ∃ y : RealVector4, w = localizedWeight W δ y}

/-- The actual localized pieces after arbitrary Euclidean linear isometries. -/
def localizedIsometryWeightFamily (weights : Set (RealVector4 → ℂ)) (δ : ℝ) :
    Set (RealVector4 → ℂ) :=
  {w | ∃ V ∈ localizedWeightFamily weights δ,
    ∃ e : RealVector4 ≃ₗᵢ[ℝ] RealVector4, w = V ∘ e}

/-- Exactly the localized pieces for which the second alternative of the
source lemma is needed. -/
def localizedZeroWeightFamily (F : RealVector4 → ℝ)
    (weights : Set (RealVector4 → ℂ)) (δ : ℝ) : Set (RealVector4 → ℂ) :=
  {w | w ∈ localizedWeightFamily weights δ ∧ ∃ x ∈ tsupport w, F x = 0}

/-- A linear isometry preserves the class of actual smooth weights. -/
theorem IsSmoothWeight.comp_realIsometry
    {w : RealVector4 → ℂ} (hw : IsSmoothWeight w)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) : IsSmoothWeight (w ∘ e) := by
  refine ⟨hw.1.comp e.toContinuousLinearEquiv.contDiff, ?_⟩
  exact hw.2.comp_homeomorph e.toHomeomorph

/-- Closed support under an isometry is its actual inverse image. -/
theorem tsupport_comp_realIsometry (w : RealVector4 → ℂ)
    (e : RealVector4 ≃ₗᵢ[ℝ] RealVector4) :
    tsupport (w ∘ e) = e ⁻¹' tsupport w := by
  change closure (Function.support (w ∘ e)) = e ⁻¹' closure (Function.support w)
  rw [Function.support_comp_eq_preimage]
  exact (e.toHomeomorph.preimage_closure (Function.support w)).symm

/-- Every fixed-scale localized piece remains an actual smooth weight. -/
theorem localizedWeightFamily_isSmoothWeight
    (weights : Set (RealVector4 → ℂ))
    (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ w ∈ localizedWeightFamily weights δ, IsSmoothWeight w := by
  rintro w ⟨W, hW, y, rfl⟩
  exact localizedWeight_isSmoothWeight W (hweights W hW) δ hδ y

/-- Localization retains the original common Euclidean support radius. -/
theorem localizedWeightFamily_support_bound
    (weights : Set (RealVector4 → ℂ)) (B : ℝ)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ‖x‖ ≤ B)
    (δ : ℝ) :
    ∀ w ∈ localizedWeightFamily weights δ, ∀ x ∈ tsupport w, ‖x‖ ≤ B := by
  rintro w ⟨W, hW, y, rfl⟩ x hx
  exact hsupport W hW x (localizedWeight_tsupport_subset W δ y hx)

/-- Smoothness survives all the orthogonal choices simultaneously. -/
theorem localizedIsometryWeightFamily_isSmoothWeight
    (weights : Set (RealVector4 → ℂ))
    (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ w ∈ localizedIsometryWeightFamily weights δ, IsSmoothWeight w := by
  rintro w ⟨V, hV, e, rfl⟩
  exact (localizedWeightFamily_isSmoothWeight weights hweights δ hδ V hV).comp_realIsometry e

/-- The support radius is unchanged by all orthogonal choices. -/
theorem localizedIsometryWeightFamily_support_bound
    (weights : Set (RealVector4 → ℂ)) (B : ℝ)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ‖x‖ ≤ B)
    (δ : ℝ) :
    ∀ w ∈ localizedIsometryWeightFamily weights δ,
      ∀ x ∈ tsupport w, ‖x‖ ≤ B := by
  rintro w ⟨V, hV, e, rfl⟩ x hx
  rw [tsupport_comp_realIsometry] at hx
  simpa only [e.norm_map] using
    localizedWeightFamily_support_bound weights B hsupport δ V hV (e x) hx

/-- One positive derivative-bound sequence controls every transformed
piece; it is selected before the weight, center, and isometry. -/
theorem localizedIsometryWeightFamily_uniform_control
    (weights : Set (RealVector4 → ℂ)) (B : ℝ)
    (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ‖x‖ ≤ B)
    (hderiv : UniformCoordinateDerivatives weights)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ w ∈ localizedIsometryWeightFamily weights δ, HBWeightControl B D w := by
  apply exists_uniformHBWeightControl (localizedIsometryWeightFamily weights δ) B
    (localizedIsometryWeightFamily_isSmoothWeight weights hweights δ hδ)
    (localizedIsometryWeightFamily_support_bound weights B hsupport δ)
  exact (hderiv.localizedWeight (fun W hW => (hweights W hW).1) δ hδ).comp_realIsometry

/-- Each actual piece satisfies precisely one of the relevant alternatives:
its closed support avoids the zero set, or it belongs to the common family
on which the analytic estimates are applied. -/
theorem localizedWeight_alternative (F : RealVector4 → ℝ)
    (weights : Set (RealVector4 → ℂ)) (δ : ℝ)
    (W : RealVector4 → ℂ) (hW : W ∈ weights) (y : RealVector4) :
    (∀ x ∈ tsupport (localizedWeight W δ y), F x ≠ 0) ∨
      localizedWeight W δ y ∈ localizedZeroWeightFamily F weights δ := by
  classical
  by_cases h : ∃ x ∈ tsupport (localizedWeight W δ y), F x = 0
  · exact Or.inr ⟨⟨W, hW, y, rfl⟩, h⟩
  · exact Or.inl (fun x hx hzero => h ⟨x, hx, hzero⟩)

end QuaternaryQuadraticForms

