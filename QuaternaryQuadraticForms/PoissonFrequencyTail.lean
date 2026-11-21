import QuaternaryQuadraticForms.EuclideanFrequencyTail
import QuaternaryQuadraticForms.PoissonFrequencyArithmetic
import QuaternaryQuadraticForms.LocalizedFrequencyIntegrals
import Mathlib.Data.PNat.Interval

/-! # Large-frequency truncation in Lemma 5.2 -/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The positive moduli satisfying the strict cutoff in (5.4). -/
def poissonModuliBelow (R : ℝ) : Finset ℕ+ :=
  (Finset.Ico 1 (Nat.succPNat ⌊R⌋₊)).filter (fun c => (c : ℝ) < R)

theorem mem_poissonModuliBelow {R : ℝ} {c : ℕ+} : c ∈ poissonModuliBelow R ↔ (c : ℝ) < R := by
  rw [poissonModuliBelow, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨Finset.mem_Ico.mpr ⟨c.one_le, ?_⟩, h⟩⟩
  exact Nat.lt_succ_of_le (Nat.le_floor h.le)

private theorem card_poissonModuliBelow (R : ℝ) (hR : 0 ≤ R) :
    ((poissonModuliBelow R).card : ℝ) ≤ R := by
  apply le_trans _ (Nat.floor_le hR)
  exact_mod_cast (Finset.card_filter_le _ _).trans_eq
    (show (Finset.Ico (1 : ℕ+) (Nat.succPNat ⌊R⌋₊)).card = ⌊R⌋₊ by simp)

/-- The frequency truncation inside a single modulus of the source Poisson sum. -/
def sourceLargeFrequencyTerm (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N) (c : ℕ+)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (w : RealVector4 → ℂ) (Q U : ℝ) : ℂ :=
  ((c : ℂ)^4)⁻¹ * ∑' u : Fin 4 → ℤ, if U < integerEuclideanNorm u then
    sourceMixedCompleteSum N ξ q hqN c A u *
      deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w ((c : ℝ)/Q)
        ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u) else 0

private theorem sourceLargeFrequencyTerm_le
    (N : ℕ) (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p hp hN x, ‖ξ p hp hN x‖ ≤ 1)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N) (c : ℕ+)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (w : RealVector4 → ℂ)
    (Q U : ℝ) (hQ : 0 < Q) (hU : 1 ≤ U) (k : ℕ) (hk : 1 ≤ k) (K : ℝ) (hK : 0 < K)
    (hrapid : ∀ v : RealVector4, v ≠ 0 →
      ‖deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w ((c : ℝ) / Q) v‖ ≤
        K * ((c : ℝ) / Q)⁻¹ * ‖v‖⁻¹ ^ (k+4)) :
    ‖sourceLargeFrequencyTerm N ξ q hqN c A w Q U‖ ≤
      2592 * K * (q : ℝ)^4 * Q * (Real.sqrt q)^(k+4) / U^k := by
  let s := Real.sqrt (q : ℝ)
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hc : 0 < (c : ℝ) := by exact_mod_cast c.pos
  let L := (q : ℝ)^4 * (c : ℝ)^5 * (K * (Q / c)) * s^(k+4)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let g := fun u : Fin 4 → ℤ => if U < integerEuclideanNorm u then
    sourceMixedCompleteSum N ξ q hqN c A u *
      deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w ((c : ℝ)/Q)
        (s⁻¹ • integerRealVector u) else 0
  let f := fun u : Fin 4 → ℤ => if U < integerEuclideanNorm u then
    1 / integerEuclideanNorm u^(k+4) else 0
  obtain ⟨hf, hfU⟩ := integerEuclidean_frequency_tail k hk U hU
  have hsum : Summable (fun u => L * f u) := hf.mul_left L
  have hdom (u : Fin 4 → ℤ) : ‖g u‖ ≤ L * f u := by
    dsimp only [g, f]
    split_ifs with hu
    · have hu' : 0 < integerEuclideanNorm u := (zero_lt_one.trans_le hU).trans hu
      have hv : ‖s⁻¹ • integerRealVector u‖ = integerEuclideanNorm u / s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), div_eq_inv_mul]
        rfl
      have hr := hrapid (s⁻¹ • integerRealVector u)
        (norm_pos_iff.mp (hv.symm ▸ div_pos hu' hs))
      rw [hv, inv_div, inv_div] at hr
      rw [norm_mul]
      apply (mul_le_mul (sourceMixedCompleteSum_trivial_bound N ξ hξ q c hqN A u) hr
        (norm_nonneg _) (by positivity)).trans_eq
      dsimp only [L]
      rw [div_pow]
      ring
    · simp
  have hg : Summable (fun u => ‖g u‖) := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hdom
  have htotal : ‖∑' u, g u‖ ≤ L * (2592 / U^k) := by
    calc
      _ ≤ ∑' u, ‖g u‖ := norm_tsum_le_tsum_norm hg
      _ ≤ ∑' u, L * f u := hg.tsum_le_tsum hdom hsum
      _ ≤ _ := by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hfU hL
  change ‖((c : ℂ)^4)⁻¹ * ∑' u, g u‖ ≤ _
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left htotal (by positivity)).trans_eq
  dsimp [L, s]
  field_simp

/-- The O(1) truncation assertion of Lemma 5.2 for a given localized family.
The constant is selected before the source prime functions, modulus, scale and weight. -/
def LargeFrequencyBound (A : Matrix (Fin 4) (Fin 4) ℤ)
    (weights : Set (RealVector4 → ℂ)) (r₀ η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ),
    (∀ p hp hN x, ‖ξ p hp hN x‖ ≤ 1) →
    ∀ (q : ℕ) [NeZero q] (hqN : q.Coprime N) (B : ℝ), 9 ≤ B → (q : ℝ) ≤ B →
    ∀ w ∈ weights, let Q := B / Real.sqrt q
    let U := Real.sqrt q * B ^ η
    ‖((heathBrownNormalization Q * B^2 / (q : ℝ)^3 : ℝ) : ℂ) *
      ∑ c ∈ poissonModuliBelow (r₀*Q), sourceLargeFrequencyTerm N ξ q hqN c A w Q U‖ ≤ C

theorem DeltaIntegralBounds.largeFrequency
    {A : Matrix (Fin 4) (Fin 4) ℤ} {weights : Set (RealVector4 → ℂ)}
    {σ : (RealVector4 → ℂ) → ℂ}
    (bounds : DeltaIntegralBounds (realQuadraticValue (A.map (Int.castRingHom ℝ)))
      σ weights (Set.Ioi 0))
    {r₀ η : ℝ} (hr₀ : 1 ≤ r₀) (hη : 0 < η) : LargeFrequencyBound A weights r₀ η := by
  obtain ⟨k, hkη⟩ := exists_nat_gt (6 / η)
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    simp only [hz, Nat.cast_zero] at hkη
    linarith [div_pos (show (0 : ℝ) < 6 by norm_num) hη])
  obtain ⟨K, hK, hr⟩ := bounds.rapid (k+4) (by omega)
  obtain ⟨H, hH, hnorm⟩ := heathBrownNormalization_error_bound 1 le_rfl
  refine ⟨(H+1) * r₀ * 2592 * K, by positivity, ?_⟩
  intro N ξ hξ q _ hqN B hB hqB w hw
  let s := Real.sqrt (q : ℝ)
  let Q := B / s
  let U := s * B^η
  change ‖((heathBrownNormalization Q * B^2 / (q : ℝ)^3 : ℝ) : ℂ) *
    ∑ c ∈ poissonModuliBelow (r₀*Q), sourceLargeFrequencyTerm N ξ q hqN c A w Q U‖ ≤ _
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqpos : 0 < (q : ℝ) := zero_lt_one.trans_le hq
  have hs : 0 < s := Real.sqrt_pos.mpr hqpos
  have hs1 : 1 ≤ s := by simpa [s] using Real.sqrt_le_sqrt hq
  have hB1 : 1 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hs1 (Real.one_le_rpow hB1 hη.le)
  have hs2 : s ^ 2 = (q : ℝ) := Real.sq_sqrt hqpos.le
  have hQ : 0 < Q := div_pos hBpos hs
  have hQ3 : 3 ≤ Q := by
    apply (le_div_iff₀ hs).mpr
    have hroot : 3 ≤ Real.sqrt B :=
      (Real.le_sqrt (by norm_num) hBpos.le).mpr (by linarith)
    calc
      3*s ≤ (Real.sqrt B) * Real.sqrt B :=
        mul_le_mul hroot (Real.sqrt_le_sqrt hqB) hs.le (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hBpos.le
  have hcQ := heathBrownNormalization_pos Q hQ3
  have hnorm' : heathBrownNormalization Q ≤ H+1 := by
    have he := (le_abs_self _).trans (hnorm Q hQ3)
    rw [pow_one] at he
    linarith [div_le_self hH.le (show 1 ≤ Q by linarith)]
  let V := 2592*K*(q : ℝ)^4*Q*s^(k+4)/U^k
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hsum : ‖∑ c ∈ poissonModuliBelow (r₀*Q), sourceLargeFrequencyTerm N ξ q hqN c A w Q U‖
      ≤ (r₀*Q) * V := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _c ∈ poissonModuliBelow (r₀*Q), V := by
        apply Finset.sum_le_sum
        intro c _
        exact sourceLargeFrequencyTerm_le N ξ hξ q hqN c A w Q U hQ hU k hk K hK
          (hr w hw _ (div_pos (by exact_mod_cast c.pos) hQ))
      _ = ((poissonModuliBelow (r₀*Q)).card : ℝ) * V := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_poissonModuliBelow _ (by positivity)) hV
  have hpow : B^4 * (q : ℝ)^2 ≤ B ^ (η * k) := by
    calc
      _ ≤ B^4 * B^2 := by gcongr
      _ = B^(6 : ℝ) := by norm_cast; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB1 (by
        rw [mul_comm]; exact ((div_lt_iff₀ hη).mp hkη).le)
  have hUr : U^k = s^k * B^(η * k) := by
    dsimp [U]
    rw [mul_pow, ← Real.rpow_natCast (B^η) k, ← Real.rpow_mul hBpos.le]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((H+1)*B^2/(q : ℝ)^3) * ((r₀*Q)*V) := by gcongr
    _ = ((H+1)*r₀*2592*K) * (B^4 * (q : ℝ)^2 / B^(η*k)) := by
      dsimp only [V]
      rw [hUr, pow_add]
      dsimp only [Q]
      rw [← hs2]
      field_simp
    _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr hpow)

/-- First clause of Lemma 5.2, for the actual common localization of Lemma 2.2. -/
theorem source_large_frequency_truncation
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂)
    (weights : Set (RealVector4 → ℂ)) (hweights : ∀ w ∈ weights, IsSmoothWeight w)
    (hsupport : ∀ w ∈ weights, ∀ x ∈ tsupport w, ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂)
    (hderiv : UniformCoordinateDerivatives weights) :
    let F := realQuadraticValue (A.map (Int.castRingHom ℝ))
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ r₀ ∧
      (∀ w ∈ localizedWeightFamily weights δ, ∀ r ≥ r₀, ∀ v : RealVector4,
        deltaIntegral F w r v = 0) ∧
      ∀ η : ℝ, 0 < η → LargeFrequencyBound A (localizedZeroWeightFamily F weights δ) r₀ η := by
  dsimp only
  obtain ⟨δ, r₀, hδ, hd1, hr1, hcut, _, bounds⟩ :=
    source_delta_integrals A hA hdet ρ₁ ρ₂ hρ₁ hρ weights hweights hsupport hderiv
  exact ⟨δ, r₀, hδ, hd1, hr1, fun w hw r hr v => (hcut w hw r hr v).1,
    fun _ hη => bounds.largeFrequency hr1 hη⟩

end QuaternaryQuadraticForms
