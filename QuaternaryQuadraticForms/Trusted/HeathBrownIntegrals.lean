import QuaternaryQuadraticForms.HeathBrownIntegralDefinitions

/-!
Registered quantitative source inputs from Heath--Brown Sections 6--8. See certification/correspondence/delta_integrals.md. None of the manuscript-specific analytic deductions is assumed.
-/

noncomputable section

open QuaternaryQuadraticForms MeasureTheory
open scoped ContDiff Topology

axiom QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization :
  ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (B : ℝ) (D : ℕ → ℝ) (L : ℝ),
    0 < B → (∀ k, 0 < D k) → 0 < L →
      ∃ δ a lam : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < a ∧ 0 < lam ∧
        ∀ W : RealVector4 → ℂ, HBWeightControl B D W →
          (∀ x ∈ tsupport W, L ≤ ‖gradient (realQuadraticValue A) x‖) →
          ∀ y : RealVector4,
            (∀ x ∈ tsupport (localizedWeight W δ y), realQuadraticValue A x ≠ 0) ∨
            ∃ s : SignedCoordinateChange,
              HBC0Geometry
                (fun x => realQuadraticValue A (signedCoordinateIsometry s x)) a lam
                (fun x => localizedWeight W δ y (signedCoordinateIsometry s x))

axiom QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph :
  ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (B : ℝ) (D : ℕ → ℝ)
    (a lam : ℝ), 0 < B → (∀ k, 0 < D k) → 0 < a → 0 < lam →
      ∀ w : RealVector4 → ℂ,
        HBC0Control (realQuadraticValue A) B D a lam w →
        ∀ φ : RealVector3 → ℝ,
          HBGraphSelector (realQuadraticValue A) w a φ →
          IntegrableOn
            (fun y => w (surfaceGraph φ y) /
              (gradient (realQuadraticValue A) (surfaceGraph φ y) 0 : ℂ))
            (weightTailSupport w) ∧
          Filter.Tendsto (thinSlabIntegral (realQuadraticValue A) w)
            (𝓝[>] (0 : ℝ)) (𝓝 (hbGraphIntegral (realQuadraticValue A) w φ))

axiom QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation :
  ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (B : ℝ) (D : ℕ → ℝ)
    (a lam R : ℝ), 0 < B → (∀ k, 0 < D k) → 0 < a → 0 < lam → 0 < R →
      ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧
        ∀ w : RealVector4 → ℂ,
          HBC0Control (realQuadraticValue A) B D a lam w →
          ∀ r : ℝ, 0 < r → r ≤ R →
            ‖deltaIntegral (realQuadraticValue A) w r 0 -
              thinSlabSingularIntegral (realQuadraticValue A) w‖ ≤ C * r ^ j

axiom QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction :
  ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (B : ℝ) (D : ℕ → ℝ)
    (a lam R : ℝ), 0 < B → (∀ k, 0 < D k) → 0 < a → 0 < lam → 0 < R →
      ∃ (D' : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (C : ℝ),
        (∀ k, 0 < D' k) ∧ (∀ j N, 0 < K j N) ∧ 0 < C ∧
        ∀ w : RealVector4 → ℂ,
          HBC0Control (realQuadraticValue A) B D a lam w →
          ∀ r : ℝ, 0 < r → r ≤ R → ∀ v : RealVector4,
            DifferentiableAt ℝ (fun t => deltaIntegral (realQuadraticValue A) w t v) r ∧
            (∃ (w₁ : RealVector4 → ℂ) (f₁ : ℝ × ℝ → ℂ),
              HBC0Control (realQuadraticValue A) B D' a lam w₁ ∧
              tsupport w₁ ⊆ tsupport w ∧ HBAmplitudeControl K f₁ ∧
              ‖deltaIntegral (realQuadraticValue A) w r v‖ ≤
                C * r⁻¹ *
                  ‖hbOscillatoryIntegral (realQuadraticValue A) w₁ f₁ r (r⁻¹ • v)‖) ∧
            (∃ (w₂ : RealVector4 → ℂ) (f₂ : ℝ × ℝ → ℂ),
              HBC0Control (realQuadraticValue A) B D' a lam w₂ ∧
              tsupport w₂ ⊆ tsupport w ∧ HBAmplitudeControl K f₂ ∧
              ‖deriv (fun t => deltaIntegral (realQuadraticValue A) w t v) r‖ ≤
                C * r⁻¹ ^ 2 *
                  ‖hbOscillatoryIntegral (realQuadraticValue A) w₂ f₂ r (r⁻¹ • v)‖)

axiom QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds :
  ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (B : ℝ) (D : ℕ → ℝ)
    (a lam R : ℝ) (K : ℕ → ℕ → ℝ),
    0 < B → (∀ k, 0 < D k) → 0 < a → 0 < lam → 0 < R →
    (∀ j N, 0 < K j N) →
      (∃ C : ℝ, 0 < C ∧ ∀ (w : RealVector4 → ℂ) (f : ℝ × ℝ → ℂ),
        HBC0Control (realQuadraticValue A) B D a lam w → HBAmplitudeControl K f →
        ∀ r : ℝ, 0 < r → r ≤ R → ∀ u : RealVector4,
          ‖hbOscillatoryIntegral (realQuadraticValue A) w f r u‖ ≤ C * r) ∧
      (∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧
        ∀ (w : RealVector4 → ℂ) (f : ℝ × ℝ → ℂ),
          HBC0Control (realQuadraticValue A) B D a lam w → HBAmplitudeControl K f →
          ∀ r : ℝ, 0 < r → r ≤ R → ∀ u : RealVector4, u ≠ 0 →
            ‖hbOscillatoryIntegral (realQuadraticValue A) w f r u‖ ≤
              C * (r⁻¹ ^ j * ‖u‖⁻¹ ^ j)) ∧
      ∀ η ε : ℝ, 0 < η → 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧
        ∀ (w : RealVector4 → ℂ) (f : ℝ × ℝ → ℂ),
          HBC0Control (realQuadraticValue A) B D a lam w → HBAmplitudeControl K f →
          (∀ x ∈ tsupport w, η ≤ |(realHessian (realQuadraticValue A) x).det|) →
          ∀ r : ℝ, 0 < r → r ≤ R → ∀ u : RealVector4, u ≠ 0 →
            ‖hbOscillatoryIntegral (realQuadraticValue A) w f r u‖ ≤
              C * ((r⁻¹ * ‖u‖) ^ ε * r * ‖u‖⁻¹)
