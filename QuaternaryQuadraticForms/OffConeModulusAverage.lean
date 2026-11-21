import QuaternaryQuadraticForms.FrequencySourceData
import QuaternaryQuadraticForms.OffConeFrequencyScales

/-! # Averaging bounded off-cone frequencies over modulus classes -/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem offCone_class_restrict
    (A : Matrix (Fin 4) (Fin 4) ℤ) (q d : ℕ) [NeZero q]
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (X U Z : ℝ) (hZ : 0 ≤ Z)
    (fourier : (Fin 4 → ℤ) → ℂ)
    (hm : ∀ u ∈ offConeFrequencies A U, modulusNormSum ξ q d A u X ≤
      Z * ‖fourier u‖ * (if (d : ℤ) ∣ integralQuadraticValue A.adjugate u then 1 else 0)) :
    ∑ u ∈ offConeFrequencies A U, modulusNormSum ξ q d A u X / integerEuclideanNorm u ≤
      Z * ∑ u ∈ divisibleEuclideanBall A d U, ‖fourier u‖ / integerEuclideanNorm u := by
  classical
  let S := (offConeFrequencies A U).filter (fun u => (d : ℤ) ∣ integralQuadraticValue A.adjugate u)
  have hsub : S ⊆ divisibleEuclideanBall A d U := by
    intro u hu
    obtain ⟨ho, hd⟩ := Finset.mem_filter.mp hu
    obtain ⟨hpos, hU, _⟩ := mem_offConeFrequencies.mp ho
    exact (mem_divisibleEuclideanBall _ _ _ _).mpr ⟨hpos, hU, hd⟩
  calc
    _ ≤ Z * ∑ u ∈ S, ‖fourier u‖ / integerEuclideanNorm u := by
      rw [show S = _ from rfl, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u hu
      apply (div_le_div_of_nonneg_right (hm u hu) (integerEuclideanNorm_nonneg u)).trans_eq
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun u _ _ => div_nonneg (norm_nonneg _) (integerEuclideanNorm_nonneg u))) hZ

/-- Apply Lemmas 3.6 and 3.11 with their constants chosen before the source data,
and sum the estimates over every divisor of q. -/
theorem source_offCone_modulus_average
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (E K r₀ η : ℝ) (hE : 1 ≤ E) (hK : 1 ≤ K) (hr : 1 ≤ r₀)
    (hη : 0 < η) (hη' : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ data : FrequencySourceData A E K,
      ∀ (q : ℕ) [NeZero q], Squarefree q → q.Coprime data.N →
      ∀ B : ℝ, 9 ≤ B → (q : ℝ) ≤ B →
      let X := r₀ * (B / Real.sqrt q)
      let U := Real.sqrt q * B^η
      (∑ d ∈ q.divisors, ∑ u ∈ offConeFrequencies A U,
        modulusNormSum (extendPrimeWeights data.N data.ξ) q d A u X / integerEuclideanNorm u) ≤
        C * (B*q)^(2*η) * (q : ℝ)^3 * B^(3*η) * ((q : ℝ)^η)^2 := by
  classical
  obtain ⟨G, hG, hmod⟩ := source_generic_modulus_bound A hA hdet η hη
  obtain ⟨L, hL, hdual⟩ := offCone_dual_growth A r₀ η hr hη hη'
  obtain ⟨P, hP, havg⟩ := source_average_frequency_bound E K η hE hK hη
  obtain ⟨D, hD, hdiv⟩ := divisors_card_le_rpow η hη
  refine ⟨D*G*L*P*2, by positivity, ?_⟩
  intro data q _ hq hqN B hB hqB
  let X := r₀ * (B / Real.sqrt q)
  let U := Real.sqrt (q : ℝ) * B^η
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hB1 : 1 ≤ B := by linarith
  have hs : 0 < Real.sqrt (q : ℝ) := by positivity
  have hs1 : 1 ≤ Real.sqrt (q : ℝ) := by simpa using Real.sqrt_le_sqrt hq1
  have hsB : Real.sqrt (q : ℝ) ≤ B := by
    exact (show Real.sqrt (q : ℝ) ≤ (q : ℝ) by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg q)]).trans hqB
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hr ((one_le_div hs).mpr hsB)
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hs1 (Real.one_le_rpow hB1 hη.le)
  let V := G * L * (B*q)^(2*η) * P * (q : ℝ)^η * (2*(q : ℝ)^3*B^(3*η))
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have H (d : ℕ) (hd : d ∈ q.divisors) :
      (∑ u ∈ offConeFrequencies A U,
        modulusNormSum (extendPrimeWeights data.N data.ξ) q d A u X / integerEuclideanNorm u) ≤ V := by
    let e := q / d
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have he0 : 0 < e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd) hd0
    letI : NeZero d := ⟨hd0.ne'⟩
    letI : NeZero e := ⟨he0.ne'⟩
    have hde : q = d*e := (Nat.mul_div_cancel' hdvd).symm
    have hde' : (q : ℝ) = (d : ℝ) * e := by exact_mod_cast hde
    have heN := hqN.of_dvd_left (show e ∣ q from hde ▸ dvd_mul_left _ _)
    let T := G * (d : ℝ)^2 * (L*(B*q)^(2*η))
    have hT : 0 ≤ T := by dsimp only [T]; positivity
    let Fourier := sourceConstrainedFourierSum data.N data.ξ e heN A
    have hm (u : Fin 4 → ℤ) (hu : u ∈ offConeFrequencies A U) :
        modulusNormSum (extendPrimeWeights data.N data.ξ) q d A u X ≤
          T * ‖Fourier u‖ * (if (d : ℤ) ∣ integralQuadraticValue A.adjugate u then 1 else 0) := by
      have h := hmod data.N data.ξ q d e hq hde hqN data.radical_dvd data.invariant data.norm_le
        u (mem_offConeFrequencies.mp hu).2.2 X hX1
      rw [constrainedFourierSum_extend_eq_source data.N data.ξ e heN] at h
      apply h.trans
      dsimp only [T, Fourier]
      change _ * _ * _ * (if (d : ℤ) ∣ integralQuadraticValue A.adjugate u then 1 else 0) * _ ≤ _
      split_ifs
      · simp only [mul_one]
        calc
          _ ≤ G * ‖sourceConstrainedFourierSum data.N data.ξ e heN A u‖ * (d : ℝ)^2 *
              (L*(B*q)^(2*η)) := by
            apply mul_le_mul_of_nonneg_left (hdual B q hB1 hq1 u hu) (by positivity)
          _ = _ := by ring
      · simp
    have ha := havg A hA hdet data.N data.N_pos data.radical_dvd data.D data.poly_nonzero data.degree_le
      data.ξ data.invariant data.fourier_bound q d e hq hde hqN U hU
    have hnumeric := offCone_average_scale (d : ℝ) e B η (by exact_mod_cast hd0)
      (by exact_mod_cast he0) hB1 hη.le
    dsimp only at hnumeric
    rw [← hde'] at hnumeric
    apply (offCone_class_restrict A q d _ X U T hT Fourier hm).trans
    apply (mul_le_mul_of_nonneg_left ha hT).trans
    calc
      _ = (G*L*(B*q)^(2*η)*P*(q : ℝ)^η) *
          ((d : ℝ)^2 * (e : ℝ)^(3/2 : ℝ) *
            (U^3/d+(e : ℝ)^(1/2 : ℝ)*U^2)) := by dsimp only [T]; ring
      _ ≤ V := mul_le_mul_of_nonneg_left hnumeric (by positivity)
  dsimp only
  calc
    _ ≤ (q.divisors.card : ℝ)*V := by simpa using Finset.sum_le_card_nsmul _ _ V H
    _ ≤ (D*(q : ℝ)^η)*V := mul_le_mul_of_nonneg_right
      (hdiv q (Nat.pos_of_ne_zero (NeZero.ne q))) hV
    _ = _ := by dsimp only [V]; ring

end QuaternaryQuadraticForms
