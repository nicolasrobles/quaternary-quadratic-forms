import QuaternaryQuadraticForms.FrequencyIntegralBounds
import QuaternaryQuadraticForms.DeltaIntegralTheorem

/-! # The common localized weights for the Section 5 frequency estimates -/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Equations (5.4)–(5.5) use the same weights, cutoff and constants for each q and B.
The zero-frequency bounds also apply to the singular integral used in Lemma 5.4. -/
theorem source_localized_frequency_integrals
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂)
    (weights : Set (RealVector4 → ℂ))
    (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂)
    (hderiv : UniformCoordinateDerivatives weights) :
    let F := realQuadraticValue (A.map (Int.castRingHom ℝ))
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ r₀ ∧
      (∀ w ∈ localizedWeightFamily weights δ, ∀ r ≥ r₀, ∀ v : RealVector4,
        deltaIntegral F w r v = 0 ∧ HasDerivAt (fun s => deltaIntegral F w s v) 0 r) ∧
      (∀ w ∈ localizedZeroWeightFamily F weights δ, ∀ v : RealVector4,
        DifferentiableOn ℝ (fun r => deltaIntegral F w r v) (Set.Ioi 0)) ∧
      (∀ η : ℝ, 0 < η → η ≤ 1/4 →
        ScaledFrequencyIntegralBound F (localizedZeroWeightFamily F weights δ) η) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ w ∈ localizedZeroWeightFamily F weights δ,
        ‖singularIntegral F w‖ ≤ C ∧ ∀ r : ℝ, 0 < r → ‖deltaIntegral F w r 0‖ ≤ C) := by
  dsimp only
  let F := realQuadraticValue (A.map (Int.castRingHom ℝ))
  obtain ⟨δ, r₀, hδ, hd1, hr1, hcut, _, bounds⟩ :=
    source_delta_integrals A hA hdet ρ₁ ρ₂ hρ₁ hρ weights hweights hsupport hderiv
  refine ⟨δ, r₀, hδ, hd1, hr1, hcut, ?_, fun _ => bounds.scaledFrequency, ?_⟩
  · intro w hw v r hr
    exact (bounds.differentiable w hw r hr v).differentiableWithinAt
  · have hr₀ : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr1
    obtain ⟨M, hM, hs⟩ := bounds.uniform_singularIntegral_norm hr₀
      (fun w hw => (hcut w hw.1 r₀ le_rfl 0).1)
    obtain ⟨K, hK, herr⟩ := bounds.zero_error 1 le_rfl
    refine ⟨M + K * r₀, by positivity, ?_⟩
    intro w hw
    refine ⟨(hs w hw).trans (le_add_of_nonneg_right (mul_nonneg hK.le hr₀.le)), ?_⟩
    intro r hr
    by_cases hc : r₀ ≤ r
    · rw [(hcut w hw.1 r hc 0).1, norm_zero]
      positivity
    · have he := herr w hw r hr
      rw [pow_one] at he
      calc
        _ ≤ ‖deltaIntegral F w r 0 - singularIntegral F w‖ + ‖singularIntegral F w‖ :=
          (sub_le_iff_le_add).mp (norm_sub_norm_le _ _)
        _ ≤ K * r + M := add_le_add he (hs w hw)
        _ ≤ M + K * r₀ := by linarith [mul_le_mul_of_nonneg_left (le_of_not_ge hc) hK.le]

end QuaternaryQuadraticForms
