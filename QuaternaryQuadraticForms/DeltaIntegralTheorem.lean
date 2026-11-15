import QuaternaryQuadraticForms.LocalizedWeightFamilies
import QuaternaryQuadraticForms.HeathBrownLocalBounds
import QuaternaryQuadraticForms.QuadraticSingularNormalization
import QuaternaryQuadraticForms.DeltaIntegralSupport
import QuaternaryQuadraticForms.DeltaIntegralUniformity
import QuaternaryQuadraticForms.DeltaIntegralIntegrability

/-!
# Lemma 2.2: the actual uniformly localized delta integrals

The common annular lower bound and the common derivative sequences are
selected first. Source localization then selects one scale for all weights
and centers. Every coordinate choice is handled by its actual nonsingular
matrix pullback, and finite-family transport supplies common constants.
The actual kernel cutoff extends the source bounded-scale estimates to
all positive scales. The singular integral is the literal normalized
Euclidean surface integral throughout the conclusion.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped ContDiff

/-- The complete analytic statement for a real symmetric nonsingular form.
The estimated family is exactly the set of pieces whose closed support
meets the zero set. Its complement is the source's nonvanishing alternative.
All constants in DeltaIntegralBounds precede every member of this family. -/
theorem source_delta_integrals_real
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂)
    (weights : Set (RealVector4 → ℂ))
    (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂)
    (hderiv : UniformCoordinateDerivatives weights) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ r₀ ∧
      (∀ w ∈ localizedWeightFamily weights δ, ∀ r : ℝ, r₀ ≤ r →
        ∀ v : RealVector4, deltaIntegral (realQuadraticValue A) w r v = 0 ∧
          HasDerivAt (fun t => deltaIntegral (realQuadraticValue A) w t v) 0 r) ∧
      (∀ w ∈ localizedZeroWeightFamily (realQuadraticValue A) weights δ,
        IntegrableOn (fun x => w x / (‖gradient (realQuadraticValue A) x‖ : ℂ))
          {x : RealVector4 | realQuadraticValue A x = 0} euclideanSurfaceMeasure) ∧
      DeltaIntegralBounds (realQuadraticValue A) (singularIntegral (realQuadraticValue A))
        (localizedZeroWeightFamily (realQuadraticValue A) weights δ) (Set.Ioi 0) := by
  have hρ₂ : 0 < ρ₂ := hρ₁.trans hρ
  have hsupp : ∀ w ∈ weights, ∀ x ∈ tsupport w, ‖x‖ ≤ ρ₂ :=
    fun w hw x hx => (hsupport w hw x hx).2
  obtain ⟨M, _hM, hFM⟩ := realQuadraticValue_abs_bound_closedBall A ρ₂
  obtain ⟨r₀, hr₀, hcutoff⟩ := deltaIntegral_uniform_cutoff (realQuadraticValue A) M
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  obtain ⟨L, hL, hgrad⟩ :=
    gradient_realQuadraticValue_annulus_lower_bound A hA hdet ρ₁ ρ₂ hρ₁
  obtain ⟨D, hD, hcontrol⟩ :=
    exists_uniformHBWeightControl weights ρ₂ hweights hsupp hderiv
  obtain ⟨δ, a, lam, hδ, hδone, ha, hlam, hlocalize⟩ :=
    Trusted.heathBrown_weight_localization A ρ₂ D L hρ₂ hD hL
  obtain ⟨Dloc, hDloc, hpieceControl⟩ :=
    localizedIsometryWeightFamily_uniform_control weights ρ₂ hweights hsupp hderiv δ hδ
  let families : SignedCoordinateChange → Set (RealVector4 → ℂ) := fun s =>
    {w | HBC0Control (fun x => realQuadraticValue A (signedCoordinateIsometry s x))
      ρ₂ Dloc a lam w}
  have hcover : ∀ w ∈ localizedZeroWeightFamily (realQuadraticValue A) weights δ,
      ∃ s : SignedCoordinateChange,
        (fun x => w (signedCoordinateIsometry s x)) ∈ families s := by
    rintro w ⟨⟨W, hW, y, rfl⟩, x, hx, hzero⟩
    have hgradient : ∀ z ∈ tsupport W, L ≤ ‖gradient (realQuadraticValue A) z‖ := by
      intro z hz
      exact hgrad z (hsupport W hW z hz).1 (hsupport W hW z hz).2
    rcases hlocalize W (hcontrol W hW) hgradient y with haway | ⟨s, hgeom⟩
    · exact False.elim (haway x hx hzero)
    · refine ⟨s, ?_, hgeom⟩
      exact hpieceControl _ ⟨localizedWeight W δ y, ⟨W, hW, y, rfl⟩,
        signedCoordinateIsometry s, rfl⟩
  have hbounded : DeltaIntegralBounds (realQuadraticValue A)
      (singularIntegral (realQuadraticValue A))
      (localizedZeroWeightFamily (realQuadraticValue A) weights δ) (Set.Ioc 0 r₀) := by
    apply DeltaIntegralBounds.of_isometry_cover
      ((realQuadraticValue_contDiff A).differentiable (by simp)) families
      (fun _ hr => hr.1) hcover
    intro s
    let e := signedCoordinateIsometry s
    let A' := realQuadraticPullbackMatrix A e
    have hA' : A'.transpose = A' := realQuadraticPullbackMatrix_symmetric A hA e
    have hdet' : A'.det ≠ 0 := realQuadraticPullbackMatrix_det_ne_zero A hdet e
    have hF' : realQuadraticValue A' = fun x => realQuadraticValue A (e x) :=
      funext (realQuadraticPullbackMatrix_value A e)
    have hthin := heathBrown_local_deltaIntegralBounds A' hA' hdet'
      ρ₂ Dloc a lam r₀ hρ₂ hDloc ha hlam hr₀pos
    have hsurface := DeltaIntegralBounds.quadraticC0_surface
      A' hA' ρ₂ Dloc a lam hρ₂ hDloc ha hlam (fun _ hw => hw) hthin
    simpa only [hF'] using hsurface
  have hcommonCutoff : ∀ w ∈ localizedWeightFamily weights δ,
      ∀ r : ℝ, r₀ ≤ r → ∀ v : RealVector4,
        deltaIntegral (realQuadraticValue A) w r v = 0 ∧
          HasDerivAt (fun t => deltaIntegral (realQuadraticValue A) w t v) 0 r := by
    intro w hw r hr v
    apply hcutoff w _ r hr v
    intro x hx
    exact hFM x (localizedWeightFamily_support_bound weights ρ₂ hsupp δ w hw x hx)
  have hintegrable := quadraticFamily_singularIntegral_integrable_of_isometry_cover
    A hA (localizedZeroWeightFamily (realQuadraticValue A) weights δ)
    ρ₂ Dloc a lam ha hlam hcover
  refine ⟨δ, r₀, hδ, hδone, hr₀, hcommonCutoff, hintegrable, ?_⟩
  exact hbounded.extend_of_cutoff hr₀
    (fun w hw r hr v => (hcommonCutoff w hw.1 r hr v).1)
    (fun w hw r hr v => (hcommonCutoff w hw.1 r hr v).2)

/-- Lemma 2.2 for the actual integral coefficient matrix in the manuscript.
The real form is evaluated by the literal coefficient embedding ℤ→ℝ. -/
theorem source_delta_integrals
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂)
    (weights : Set (RealVector4 → ℂ))
    (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂)
    (hderiv : UniformCoordinateDerivatives weights) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ r₀ ∧
      (∀ w ∈ localizedWeightFamily weights δ, ∀ r : ℝ, r₀ ≤ r →
        ∀ v : RealVector4,
          deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w r v = 0 ∧
          HasDerivAt
            (fun t => deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w t v) 0 r) ∧
      (∀ w ∈ localizedZeroWeightFamily (realQuadraticValue (A.map (Int.castRingHom ℝ))) weights δ,
        IntegrableOn
          (fun x => w x / (‖gradient (realQuadraticValue (A.map (Int.castRingHom ℝ))) x‖ : ℂ))
          {x : RealVector4 | realQuadraticValue (A.map (Int.castRingHom ℝ)) x = 0}
          euclideanSurfaceMeasure) ∧
      DeltaIntegralBounds (realQuadraticValue (A.map (Int.castRingHom ℝ)))
        (singularIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))))
        (localizedZeroWeightFamily (realQuadraticValue (A.map (Int.castRingHom ℝ))) weights δ)
        (Set.Ioi 0) := by
  have hsym : (A.map (Int.castRingHom ℝ)).transpose = A.map (Int.castRingHom ℝ) := by
    ext i j
    change (A j i : ℝ) = (A i j : ℝ)
    exact_mod_cast congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M i j) hA
  have hdetreal : (A.map (Int.castRingHom ℝ)).det ≠ 0 := by
    change ((Int.castRingHom ℝ).mapMatrix A).det ≠ 0
    rw [← (Int.castRingHom ℝ).map_det A]
    change (A.det : ℝ) ≠ 0
    exact_mod_cast hdet
  exact source_delta_integrals_real (A.map (Int.castRingHom ℝ)) hsym hdetreal
    ρ₁ ρ₂ hρ₁ hρ weights hweights hsupport hderiv

end QuaternaryQuadraticForms

