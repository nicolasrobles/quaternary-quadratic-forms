import QuaternaryQuadraticForms.DeltaIntegralBounds
import QuaternaryQuadraticForms.DeltaIntegralRescaling
import QuaternaryQuadraticForms.HeathBrownQuadraticHypotheses
import QuaternaryQuadraticForms.Trusted.HeathBrownIntegrals

/-!
# Local delta-integral estimates from the source analytic inputs

The registered zero-frequency approximation and oscillatory reduction are
combined with the source bounds for the actual auxiliary integrals. The
quadratic Hessian condition and all frequency rescaling are internal proofs.
Every constant is chosen before the weight, scale, and frequency.

The value functional here is explicitly the thin-slab singular integral.
Its identification with the manuscript's surface integral is a separate
geometric obligation.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- All local estimates on a fixed positive bounded scale range, uniformly
over the quantitative source class. Value and derivative estimates retain
their independent modified weights and amplitudes. -/
theorem heathBrown_local_deltaIntegralBounds
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (B : ℝ) (D : ℕ → ℝ) (a lam R : ℝ)
    (hB : 0 < B) (hD : ∀ k, 0 < D k) (ha : 0 < a)
    (hlam : 0 < lam) (hR : 0 < R) :
    DeltaIntegralBounds (realQuadraticValue A)
      (thinSlabSingularIntegral (realQuadraticValue A))
      {w | HBC0Control (realQuadraticValue A) B D a lam w} (Set.Ioc 0 R) := by
  obtain ⟨D', K, C, hD', hK, hC, hreduce⟩ :=
    Trusted.heathBrown_integral_reduction A B D a lam R hB hD ha hlam hR
  obtain ⟨⟨C15, hC15, h15⟩, h18, h22⟩ :=
    Trusted.heathBrown_oscillatory_bounds A B D' a lam R K hB hD' ha hlam hR hK
  obtain ⟨η, hη, hHessian⟩ :=
    realQuadraticValue_hessian_uniform_lower_bound A hA hdet
  refine {
    differentiable := ?_
    zero_error := ?_
    zero_derivative := ?_
    rapid := ?_
    decay := ?_
  }
  · intro w hw r hr v
    exact (hreduce w hw r hr.1 hr.2 v).1
  · intro j hj
    obtain ⟨C0, hC0, hzero⟩ :=
      Trusted.heathBrown_zero_approximation A B D a lam R hB hD ha hlam hR j hj
    exact ⟨C0, hC0, fun w hw r hr => hzero w hw r hr.1 hr.2⟩
  · refine ⟨C * C15, mul_pos hC hC15, ?_⟩
    intro w hw r hr
    obtain ⟨w₂, f₂, hw₂, _, hf₂, hderiv⟩ :=
      (hreduce w hw r hr.1 hr.2 0).2.2
    have hJ := h15 w₂ f₂ hw₂ hf₂ r hr.1 hr.2 (r⁻¹ • 0)
    calc
      ‖deriv (fun t => deltaIntegral (realQuadraticValue A) w t 0) r‖ ≤
          C * r⁻¹ ^ 2 *
            ‖hbOscillatoryIntegral (realQuadraticValue A) w₂ f₂ r (r⁻¹ • 0)‖ :=
        hderiv
      _ ≤ C * r⁻¹ ^ 2 * (C15 * r) :=
        mul_le_mul_of_nonneg_left hJ (mul_nonneg hC.le (sq_nonneg _))
      _ = C * C15 * r⁻¹ := by field_simp [hr.1.ne']
  · intro j hj
    obtain ⟨C18, hC18, hrapid⟩ := h18 j hj
    refine ⟨C * C18, mul_pos hC hC18, ?_⟩
    intro w hw r hr v hv
    have hu : r⁻¹ • v ≠ 0 := smul_ne_zero (inv_ne_zero hr.1.ne') hv
    obtain ⟨w₁, f₁, hw₁, _, hf₁, hvalue⟩ :=
      (hreduce w hw r hr.1 hr.2 v).2.1
    have hJ := hrapid w₁ f₁ hw₁ hf₁ r hr.1 hr.2 (r⁻¹ • v) hu
    have hscale :
        r⁻¹ * (r⁻¹ ^ j * ‖r⁻¹ • v‖⁻¹ ^ j) = r⁻¹ * ‖v‖⁻¹ ^ j := by
      simpa only [inv_pow] using deltaIntegral_rapid_scale_identity hr.1 v j
    calc
      ‖deltaIntegral (realQuadraticValue A) w r v‖ ≤
          C * r⁻¹ *
            ‖hbOscillatoryIntegral (realQuadraticValue A) w₁ f₁ r (r⁻¹ • v)‖ :=
        hvalue
      _ ≤ C * r⁻¹ * (C18 * (r⁻¹ ^ j * ‖r⁻¹ • v‖⁻¹ ^ j)) :=
        mul_le_mul_of_nonneg_left hJ
          (mul_nonneg hC.le (inv_nonneg.mpr hr.1.le))
      _ = (C * C18) * (r⁻¹ * (r⁻¹ ^ j * ‖r⁻¹ • v‖⁻¹ ^ j)) := by ring
      _ = (C * C18) * (r⁻¹ * ‖v‖⁻¹ ^ j) := by rw [hscale]
      _ = (C * C18) * r⁻¹ * ‖v‖⁻¹ ^ j := by ring
  · intro ε hε hεhalf
    obtain ⟨C22, hC22, hdecay⟩ := h22 η ε hη hε hεhalf
    refine ⟨2 * (C * C22), mul_pos (by norm_num) (mul_pos hC hC22), ?_⟩
    intro w hw r hr v hv
    have hu : r⁻¹ • v ≠ 0 := smul_ne_zero (inv_ne_zero hr.1.ne') hv
    obtain ⟨_, ⟨w₁, f₁, hw₁, _, hf₁, hvalue⟩,
        ⟨w₂, f₂, hw₂, _, hf₂, hderiv⟩⟩ := hreduce w hw r hr.1 hr.2 v
    have hJ₁ := hdecay w₁ f₁ hw₁ hf₁ (fun x _ => hHessian x)
      r hr.1 hr.2 (r⁻¹ • v) hu
    have hJ₂ := hdecay w₂ f₂ hw₂ hf₂ (fun x _ => hHessian x)
      r hr.1 hr.2 (r⁻¹ • v) hu
    let E : ℝ := (r⁻¹ * ‖r⁻¹ • v‖) ^ ε * r * ‖r⁻¹ • v‖⁻¹
    have hI : ‖deltaIntegral (realQuadraticValue A) w r v‖ ≤
        (C * C22) / r * E := by
      calc
        ‖deltaIntegral (realQuadraticValue A) w r v‖ ≤
            C * r⁻¹ *
              ‖hbOscillatoryIntegral (realQuadraticValue A) w₁ f₁ r (r⁻¹ • v)‖ :=
          hvalue
        _ ≤ C * r⁻¹ * (C22 * E) :=
          mul_le_mul_of_nonneg_left hJ₁
            (mul_nonneg hC.le (inv_nonneg.mpr hr.1.le))
        _ = (C * C22) / r * E := by rw [div_eq_mul_inv]; ring
    have hDvalue :
        ‖deriv (fun t => deltaIntegral (realQuadraticValue A) w t v) r‖ ≤
          (C * C22) / r ^ 2 * E := by
      calc
        ‖deriv (fun t => deltaIntegral (realQuadraticValue A) w t v) r‖ ≤
            C * r⁻¹ ^ 2 *
              ‖hbOscillatoryIntegral (realQuadraticValue A) w₂ f₂ r (r⁻¹ • v)‖ :=
          hderiv
        _ ≤ C * r⁻¹ ^ 2 * (C22 * E) :=
          mul_le_mul_of_nonneg_left hJ₂ (mul_nonneg hC.le (sq_nonneg _))
        _ = (C * C22) / r ^ 2 * E := by
          rw [div_eq_mul_inv, ← inv_pow]
          ring
    have hcombined := deltaIntegral_combine_value_derivative_bounds hr.1 hI hDvalue
    have hscale : r⁻¹ * E = r ^ (1 - 2 * ε) * ‖v‖ ^ (-1 + ε) :=
      deltaIntegral_epsilon_scale_identity hr.1 hv ε
    calc
      ‖deltaIntegral (realQuadraticValue A) w r v‖ +
          r * ‖deriv (fun t => deltaIntegral (realQuadraticValue A) w t v) r‖ ≤
          ((C * C22) + (C * C22)) * (r⁻¹ * E) := hcombined
      _ = (2 * (C * C22)) * r ^ (1 - 2 * ε) * ‖v‖ ^ (-1 + ε) := by
        rw [hscale]
        ring

end QuaternaryQuadraticForms
