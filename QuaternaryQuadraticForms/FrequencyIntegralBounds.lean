import QuaternaryQuadraticForms.DeltaIntegralBounds
import QuaternaryQuadraticForms.PoissonDefinitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Integral bounds at the actual Poisson frequencies in Section 5 -/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The scaled estimate in (5.5), uniformly over the localized weights and moduli.
The derivative acts on the original scale with the scaled lattice frequency fixed. -/
def ScaledFrequencyIntegralBound (F : RealVector4 → ℝ)
    (weights : Set (RealVector4 → ℂ)) (η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ w ∈ weights, ∀ (q : ℕ), 1 ≤ q → ∀ B : ℝ, 1 ≤ B →
    ∀ t : ℝ, 1 ≤ t → ∀ u : Fin 4 → ℤ, 0 < integerEuclideanNorm u →
    integerEuclideanNorm u ≤ Real.sqrt q * B ^ η →
    let r := t / (B / Real.sqrt q)
    let v := (Real.sqrt q)⁻¹ • integerRealVector u
    ‖deltaIntegral F w r v‖ + r * ‖deriv (fun s => deltaIntegral F w s v) r‖ ≤
      C * (t * q / (B * integerEuclideanNorm u)) * B ^ (3 * η)

/-- Rescale the localized decay estimate from Lemma 2.2 at u/√q and t/Q. -/
theorem DeltaIntegralBounds.scaledFrequency {F : RealVector4 → ℝ}
    {σ : (RealVector4 → ℂ) → ℂ} {weights : Set (RealVector4 → ℂ)}
    (bounds : DeltaIntegralBounds F σ weights (Set.Ioi 0))
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/4) : ScaledFrequencyIntegralBound F weights η := by
  obtain ⟨C, hC, hdecay⟩ := bounds.decay η hη (by linarith)
  refine ⟨C, hC, ?_⟩
  intro w hw q hq B hB t ht u hu hU
  let s := Real.sqrt (q : ℝ)
  let r := t / (B / s)
  let v := s⁻¹ • integerRealVector u
  change ‖deltaIntegral F w r v‖ + r * ‖deriv (fun x => deltaIntegral F w x v) r‖ ≤ _
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs1 : 1 ≤ s := by simpa [s] using (Real.sqrt_le_sqrt hq')
  have hs : 0 < s := by linarith
  have hs2 : s ^ 2 = (q : ℝ) := Real.sq_sqrt (by positivity)
  have hB' : 0 < B := by linarith
  have ht' : 0 < t := by linarith
  have hr : 0 < r := div_pos ht' (div_pos hB' hs)
  have hv : ‖v‖ = integerEuclideanNorm u / s := by
    rw [show v = s⁻¹ • integerRealVector u from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs), div_eq_inv_mul]
    rfl
  have hz : 0 < ‖v‖ := hv.symm ▸ div_pos hu hs
  have hvB : ‖v‖ ≤ B := by
    rw [hv, div_le_iff₀ hs]
    calc
      integerEuclideanNorm u ≤ s * B ^ η := hU
      _ ≤ s * B ^ (1 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) hs.le
      _ = B * s := by rw [Real.rpow_one, mul_comm]
  have hrB : r⁻¹ ≤ B := by
    dsimp [r]
    rw [inv_div, div_le_iff₀ ht']
    exact (div_le_self hB'.le hs1).trans (le_mul_of_one_le_right hB'.le ht)
  have hscale : r / ‖v‖ = t * (q : ℝ) / (B * integerEuclideanNorm u) := by
    rw [hv, ← hs2]
    dsimp [r]
    field_simp
  calc
    _ ≤ C * r ^ (1 - 2 * η) * ‖v‖ ^ (-1 + η) :=
      hdecay w hw r hr v (norm_pos_iff.mp hz)
    _ = C * (r / ‖v‖) * (r⁻¹) ^ (2 * η) * ‖v‖ ^ η := by
      rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one,
        Real.rpow_neg_eq_inv_rpow, Real.rpow_add hz, Real.rpow_neg_one]
      ring
    _ ≤ C * (r / ‖v‖) * B ^ (2 * η) * B ^ η := by
      gcongr
    _ = _ := by
      rw [hscale, mul_assoc (C * _) , ← Real.rpow_add hB']
      ring_nf

/-- The common kernel cutoff and the zero-frequency estimate in Lemma 2.2
bound the actual singular integral uniformly on the localized family. -/
theorem DeltaIntegralBounds.uniform_singularIntegral_norm {F : RealVector4 → ℝ}
    {σ : (RealVector4 → ℂ) → ℂ} {weights : Set (RealVector4 → ℂ)}
    (bounds : DeltaIntegralBounds F σ weights (Set.Ioi 0))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcut : ∀ w ∈ weights, deltaIntegral F w r₀ 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ weights, ‖σ w‖ ≤ C := by
  obtain ⟨K, hK, herror⟩ := bounds.zero_error 1 le_rfl
  refine ⟨K * r₀, mul_pos hK hr₀, ?_⟩
  intro w hw
  simpa [hcut w hw] using herror w hw r₀ hr₀

/-- The small-modulus estimate in Lemma 5.4, with one constant for all Q,c and weights. -/
theorem DeltaIntegralBounds.small_modulus_zero_error {F : RealVector4 → ℝ}
    {σ : (RealVector4 → ℂ) → ℂ} {weights : Set (RealVector4 → ℂ)}
    (bounds : DeltaIntegralBounds F σ weights (Set.Ioi 0)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ weights, ∀ Q : ℝ, 1 ≤ Q → ∀ c : ℕ+, (c : ℝ) ≤ Q ^ (1 - η) →
      ‖deltaIntegral F w ((c : ℝ) / Q) 0 - σ w‖ ≤ C / Q ^ 2 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / η)
  have hj' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    simp only [hz, Nat.cast_zero] at hj
    linarith [div_pos (show (0 : ℝ) < 2 by norm_num) hη])
  obtain ⟨C, hC, herror⟩ := bounds.zero_error j hj'
  refine ⟨C, hC, ?_⟩
  intro w hw Q hQ c hc
  have hQ' : 0 < Q := zero_lt_one.trans_le hQ
  have hc' : 0 < (c : ℝ) := by exact_mod_cast c.pos
  have hr : 0 < (c : ℝ) / Q := div_pos hc' hQ'
  have hcut : (c : ℝ) / Q ≤ Q ^ (-η) := by
    rw [div_le_iff₀ hQ']
    simpa [sub_eq_add_neg, Real.rpow_add hQ', mul_comm] using hc
  have hjη : 2 < (j : ℝ) * η := (div_lt_iff₀ hη).mp hj
  calc
    _ ≤ C * ((c : ℝ) / Q)^j := herror w hw _ hr
    _ ≤ C * (Q ^ (-η)) ^ j := by gcongr
    _ = C * Q ^ (-η * j) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ'.le]
    _ ≤ C * Q ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ (by
        rw [neg_mul, mul_comm η]
        exact neg_le_neg hjη.le)) hC.le
    _ = C / Q ^ 2 := by rw [Real.rpow_neg hQ'.le, Real.rpow_two, div_eq_mul_inv]

end QuaternaryQuadraticForms
