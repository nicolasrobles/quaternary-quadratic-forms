import QuaternaryQuadraticForms.OffConeModulusAverage

/-! # Lemma 5.2 for the actual large and bounded off-cone frequencies -/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The second source estimate for the finite off-cone ball with its Poisson prefactor. -/
def BoundedOffConeBound (A : Matrix (Fin 4) (Fin 4) ℤ) (E K : ℝ)
    (weights : Set (RealVector4 → ℂ)) (r₀ η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ data : FrequencySourceData A E K,
    ∀ (q : ℕ) [NeZero q], Squarefree q → ∀ hqN : q.Coprime data.N,
    ∀ B : ℝ, 9 ≤ B → (q : ℝ) ≤ B → ∀ w ∈ weights,
    let Q := B / Real.sqrt q
    ‖((heathBrownNormalization Q * B^2 / (q : ℝ)^3 : ℝ) : ℂ) *
      sourceBoundedOffConeSum data.N data.ξ q hqN A w (r₀*Q) Q (Real.sqrt q * B^η)‖ ≤
        C * (B*q)^(1+8*η)

theorem ScaledFrequencyIntegralBound.boundedOffCone
    {A : Matrix (Fin 4) (Fin 4) ℤ} (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (E K : ℝ) (hE : 1 ≤ E) (hK : 1 ≤ K)
    {weights : Set (RealVector4 → ℂ)} {r₀ η : ℝ} (hr : 1 ≤ r₀) (hη : 0 < η)
    (hη' : η ≤ 1/4) (bounds : ScaledFrequencyIntegralBound
      (realQuadraticValue (A.map (Int.castRingHom ℝ))) weights η) :
    BoundedOffConeBound A E K weights r₀ η := by
  obtain ⟨J, hJ, hred⟩ := bounds.offCone_modulus_reduction
  obtain ⟨C, hC, hav⟩ := source_offCone_modulus_average A hA hdet E K r₀ η hE hK hr hη hη'
  obtain ⟨H, hH, hnorm⟩ := heathBrownNormalization_error_bound 1 le_rfl
  refine ⟨(H+1)*J*C, by positivity, ?_⟩
  intro data q _ hq hqN B hB hqB w hw
  let Q := B / Real.sqrt q
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqpos : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hB1 : 1 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hroot : 3 ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) hBpos.le).mpr (by linarith)
  have hQ3 : 3 ≤ Q := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hqpos)).mpr
    exact (mul_le_mul hroot (Real.sqrt_le_sqrt hqB) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt hBpos.le)
  have hn := heathBrownNormalization_pos Q hQ3
  have hn' : heathBrownNormalization Q ≤ H+1 := by
    have he := (le_abs_self _).trans (hnorm Q hQ3)
    rw [pow_one] at he
    linarith [div_le_self hH.le (show 1 ≤ Q by linarith)]
  have hsum := hred data.N data.ξ q hqN B (r₀*Q) hB1 w hw
  have htotal := hav data q hq hqN B hB hqB
  dsimp only at hsum htotal ⊢
  have hpow : (B*q)^(1+8*η) = (B*q) * ((B*q)^(2*η)) * B^(6*η) * (q : ℝ)^(6*η) := by
    rw [show 1+8*η = 1+2*η+6*η by ring, Real.rpow_add (mul_pos hBpos hqpos),
      Real.rpow_add (mul_pos hBpos hqpos), Real.rpow_one, Real.mul_rpow hBpos.le hqpos.le (z := 6*η)]
    ring
  have hqη : ((q : ℝ)^η)^2 ≤ (q : ℝ)^(6*η) := by
    rw [← Real.rpow_natCast ((q : ℝ)^η) 2, ← Real.rpow_mul hqpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    norm_num
    linarith
  have hB6 : B^(3*η) * B^(3*η) = B^(6*η) := by
    rw [← Real.rpow_add hBpos]; ring_nf
  change ‖((heathBrownNormalization Q * B^2 / (q : ℝ)^3 : ℝ) : ℂ) * _‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((H+1)*B^2/(q : ℝ)^3) *
        ((J*q/B*B^(3*η)) * (C*(B*q)^(2*η)*(q : ℝ)^3*B^(3*η)*((q : ℝ)^η)^2)) := by
      apply mul_le_mul _ (hsum.trans (mul_le_mul_of_nonneg_left htotal (by positivity)))
        (norm_nonneg _) (by positivity)
      gcongr
    _ = ((H+1)*J*C)*((B*q)*(B*q)^(2*η)*B^(6*η))*((q : ℝ)^η)^2 := by
      rw [← hB6]
      field_simp
    _ ≤ ((H+1)*J*C)*((B*q)*(B*q)^(2*η)*B^(6*η))*(q : ℝ)^(6*η) :=
      mul_le_mul_of_nonneg_left hqη (by positivity)
    _ = _ := by rw [hpow]; ring

/-- Complete Lemma 5.2. The two estimates use the very same localization and modulus cutoff. -/
theorem source_offcone
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂)
    (weights : Set (RealVector4 → ℂ)) (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂)
    (hderiv : UniformCoordinateDerivatives weights) :
    let F := realQuadraticValue (A.map (Int.castRingHom ℝ))
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ r₀ ∧
      (∀ w ∈ localizedWeightFamily weights δ, ∀ r ≥ r₀, ∀ v : RealVector4,
        deltaIntegral F w r v = 0) ∧
      ∀ E K η : ℝ, 1 ≤ E → 1 ≤ K → 0 < η → η ≤ 1/4 →
        LargeFrequencyBound A (localizedZeroWeightFamily F weights δ) r₀ η ∧
        BoundedOffConeBound A E K (localizedZeroWeightFamily F weights δ) r₀ η := by
  dsimp only
  obtain ⟨δ, r₀, hδ, hd1, hr₀, hcut, _, bounds⟩ :=
    source_delta_integrals A hA hdet ρ₁ ρ₂ hρ₁ hρ weights hweights hsupport hderiv
  refine ⟨δ, r₀, hδ, hd1, hr₀, fun w hw r hr v => (hcut w hw r hr v).1, ?_⟩
  intro E K η hE hK hη hη'
  exact ⟨bounds.largeFrequency hr₀ hη,
    (bounds.scaledFrequency hη hη').boundedOffCone hA hdet E K hE hK hr₀ hη hη'⟩

end QuaternaryQuadraticForms
