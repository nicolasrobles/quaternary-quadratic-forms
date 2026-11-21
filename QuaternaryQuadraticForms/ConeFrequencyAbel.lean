import QuaternaryQuadraticForms.ConeModulusTheorem
import QuaternaryQuadraticForms.LocalizedFrequencyIntegrals
import QuaternaryQuadraticForms.OrderedSeriesTail
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Partial summation of the moduli on the dual cone -/

noncomputable section
open Finset MeasureTheory

namespace QuaternaryQuadraticForms

private theorem sum_gcd_weight (q d : ℕ) (a : ℕ → ℂ) (f : ℝ → ℂ) (X : ℝ) :
    ∑ k ∈ Icc 0 ⌊X⌋₊, f k * (if 1 ≤ k ∧ k.gcd q = d then a k else 0) =
      ∑ k ∈ gcdModuliUpTo q d ⌊X⌋₊, f k * a k := by
  classical
  simp_rw [mul_ite, mul_zero, ← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc, Nat.zero_le, true_and, mem_gcdModuliUpTo]
  tauto

/-- Abel summation up to the common support endpoint. Cancellation in the
unweighted complete sums is taken before the absolute value. -/
theorem cone_modulus_abel_bound (A : Matrix (Fin 4) (Fin 4) ℤ) (q d : ℕ)
    (u : Fin 4 → ℤ) (f : ℝ → ℂ) {X η K L : ℝ} (hX : 1 ≤ X) (hη : 0 < η)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hzero : f X = 0)
    (hdiff : ∀ t ∈ Set.Icc 1 X, DifferentiableAt ℝ f t)
    (hderiv : ∀ t ∈ Set.Icc 1 X, ‖deriv f t‖ ≤ L / t^4)
    (hsum : ∀ t ∈ Set.Icc 1 X, ‖unweightedModulusSum q d A u t‖ ≤ K*t^(3+η)) :
    ‖∑ k ∈ gcdModuliUpTo q d ⌊X⌋₊, f k * unweightedCompleteSumValue k A u‖ ≤
      L*K*X^η/η := by
  let a : ℕ → ℂ := fun k => if 1 ≤ k ∧ k.gcd q = d then unweightedCompleteSumValue k A u else 0
  have hac (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, a k = unweightedModulusSum q d A u t := by
    simpa only [one_mul, a] using sum_gcd_weight q d (fun k => unweightedCompleteSumValue k A u) (fun _ => 1) t
  have hi : IntegrableOn (deriv f) (Set.Icc 1 X) := by
    apply Measure.integrableOn_of_bounded (M := L) (measure_Icc_lt_top.ne) (aestronglyMeasurable_deriv _ _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hderiv t ht).trans (div_le_self hL (one_le_pow₀ ht.1))
  have heq := sum_mul_eq_sub_integral_mul₀ a (by simp [a]) X hdiff hi
  rw [hzero, zero_mul, zero_sub] at heq
  simp_rw [hac] at heq
  rw [← sum_gcd_weight q d _ f X]
  change ‖∑ k ∈ Icc 0 ⌊X⌋₊, f k * a k‖ ≤ _
  rw [heq, norm_neg]
  have hI := intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := X) (r := η-1) (by linarith)
  calc
    _ ≤ ∫ t in Set.Ioc 1 X, (L*K)*t^(η-1) := by
      apply norm_integral_le_of_norm_le (hI.1.const_mul (L*K))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Set.Icc 1 X := ⟨ht.1.le,ht.2⟩
      have hpos : 0 < t := zero_lt_one.trans ht.1
      rw [norm_mul]
      calc
        _ ≤ (L/t^4)*(K*t^(3+η)) := mul_le_mul (hderiv t ht') (hsum t ht') (norm_nonneg _) (by positivity)
        _ = (L*K)*t^(η-1) := by
          rw [← Real.rpow_natCast t 4, div_eq_mul_inv, ← Real.rpow_neg hpos.le]
          norm_num only [Nat.cast_ofNat]
          rw [show L*t^(-(4:ℝ))*(K*t^(3+η)) = L*K*(t^(-(4:ℝ))*t^(3+η)) by ring,
            ← Real.rpow_add hpos, show -(4:ℝ)+(3+η) = η-1 by ring]
    _ = (L*K)*((X^η-1)/η) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hX, integral_rpow (Or.inl (by linarith)),
        sub_add_cancel, Real.one_rpow]
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hη.le) (mul_nonneg hL hK)

/-- The weight in the on-cone modulus sum, with its frequency fixed. -/
def coneIntegralWeight (I : ℝ → ℂ) (Q t : ℝ) : ℂ := (t^4)⁻¹ • I (t/Q)

private theorem coneIntegralWeight_hasDerivAt (I : ℝ → ℂ) {t Q : ℝ}
    (ht : 0 < t) (hI : DifferentiableAt ℝ I (t/Q)) :
    HasDerivAt (coneIntegralWeight I Q)
      ((t^4)⁻¹ • (Q⁻¹ • deriv I (t/Q)) + (-(4/t^5)) • I (t/Q)) t := by
  have hpow : HasDerivAt (fun x : ℝ => (x^4)⁻¹) (-(4/t^5)) t := by
    convert ((hasDerivAt_pow 4 t).inv (pow_ne_zero _ ht.ne')) using 1
    field_simp
    ring
  have hdiv : HasDerivAt (fun x : ℝ => x/Q) Q⁻¹ t := by
    simpa using (hasDerivAt_id t).div_const Q
  exact hpow.smul (hI.hasDerivAt.scomp t hdiv)

/-- The derivative bound for the partial-summation weight follows at the
real scale t/Q. Its complex delta integral is differentiated at fixed v. -/
theorem coneIntegralWeight_derivative (I : ℝ → ℂ) {t Q L : ℝ}
    (ht : 0 < t) (hQ : 0 < Q) (hI : DifferentiableAt ℝ I (t/Q))
    (hb : ‖I (t/Q)‖ + (t/Q) * ‖deriv I (t/Q)‖ ≤ L*t) :
    DifferentiableAt ℝ (coneIntegralWeight I Q) t ∧
    ‖deriv (coneIntegralWeight I Q) t‖ ≤ 4*L/t^4 := by
  have hd := coneIntegralWeight_hasDerivAt I ht hI
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr (pow_pos ht 4)),
    abs_of_pos (inv_pos.mpr hQ), abs_of_pos (div_pos (by norm_num : (0:ℝ)<4) (pow_pos ht 5))]
  have hh : (t/Q) * ‖deriv I (t/Q)‖ + 4*‖I (t/Q)‖ ≤ 4*(L*t) := by
    linarith [mul_nonneg (div_nonneg ht.le hQ.le) (norm_nonneg (deriv I (t/Q)))]
  calc
    _ = ((t/Q) * ‖deriv I (t/Q)‖ + 4*‖I (t/Q)‖) / t^5 := by field_simp
    _ ≤ (4*(L*t))/t^5 := div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

/-- The inner modulus sum of Lemma 5.3, for each individual gcd class and
nonzero dual-cone frequency. The constant is uniform in all arithmetic data. -/
theorem DeltaIntegralBounds.onCone_modulus_sum
    {A : Matrix (Fin 4) (Fin 4) ℤ} (hA : A.transpose = A) (hd : A.det ≠ 0)
    (hns : ¬IsSquare A.det) {weights : Set (RealVector4 → ℂ)}
    {σ : (RealVector4 → ℂ) → ℂ} {r₀ η : ℝ} (hr : 1 ≤ r₀) (hη : 0 < η) (hη' : η ≤ 1/4)
    (bounds : DeltaIntegralBounds (realQuadraticValue (A.map (Int.castRingHom ℝ))) σ weights (Set.Ioi 0))
    (hcut : ∀ w ∈ weights, ∀ v, deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w r₀ v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ weights, ∀ (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e],
      Squarefree q → q = d*e → q.Coprime (quadraticBadPrimeModulus A) →
      ∀ (B : ℝ), 1 ≤ B → 1 ≤ B / Real.sqrt q →
      ∀ (u : Fin 4 → ℤ), dotProduct u (A.adjugate.mulVec u) = 0 →
      0 < integerEuclideanNorm u → integerEuclideanNorm u ≤ Real.sqrt q * B^η →
      let Q := B/Real.sqrt q
      let I := fun r => deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w r
        ((Real.sqrt q)⁻¹ • integerRealVector u)
      ‖∑ c ∈ gcdModuliUpTo q d ⌊r₀*Q⌋₊, coneIntegralWeight I Q c * unweightedCompleteSumValue c A u‖ ≤
        C * ((q:ℝ)/(B * integerEuclideanNorm u)) * B^(3*η) * (B*q)^η := by
  obtain ⟨J,hJ,hscaled⟩ := bounds.scaledFrequency hη hη'
  obtain ⟨K,hK,hmod⟩ := source_cone_modulus_bound A hA hd hns η hη
  have hr0 : 0 < r₀ := zero_lt_one.trans_le hr
  refine ⟨4*J*K*r₀^η/η, by positivity, ?_⟩
  intro w hw q d e _ _ _ hsq hqe hgood B hB hQ u hu hu0 hU
  let Q := B/Real.sqrt q
  let X := r₀*Q
  let v := (Real.sqrt q)⁻¹ • integerRealVector u
  let I := fun r => deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w r v
  let L := J*((q:ℝ)/(B*integerEuclideanNorm u))*B^(3*η)
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1' : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hr hQ
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hD (t : ℝ) (ht : t ∈ Set.Icc 1 X) := by
    have ht0 := zero_lt_one.trans_le ht.1
    have hb := hscaled w hw q hq1 B hB t ht.1 u hu0 hU
    change ‖I (t/Q)‖ + (t/Q)*‖deriv I (t/Q)‖ ≤ J * (t*q/(B*integerEuclideanNorm u))*B^(3*η) at hb
    exact coneIntegralWeight_derivative I ht0 hQ0
      (bounds.differentiable w hw _ (div_pos ht0 hQ0) v) (L := L) (hb.trans_eq (by dsimp [L]; ring))
  have hKq : 0 ≤ K*(q:ℝ)^η := by positivity
  have hab := cone_modulus_abel_bound A q d u (coneIntegralWeight I Q) hX hη hKq
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hL) (by
      unfold coneIntegralWeight
      rw [show X/Q = r₀ by dsimp [X]; field_simp, show I r₀ = 0 from hcut w hw v, smul_zero])
    (fun t ht => (hD t ht).1) (fun t ht => (hD t ht).2) (fun t ht => by
      have ht0 := zero_lt_one.trans_le ht.1
      apply (hmod q d e hsq hqe hgood u hu t ht.1).trans_eq
      rw [Real.mul_rpow ht0.le (Nat.cast_nonneg q), Real.rpow_add ht0, Real.rpow_ofNat]
      ring)
  have hQB : Q ≤ B := div_le_self hB0.le (by simpa using Real.sqrt_le_sqrt hq1')
  have hXB : X^η ≤ r₀^η*B^η := by
    rw [← Real.mul_rpow hr0.le hB0.le]
    exact Real.rpow_le_rpow (by positivity : 0 ≤ r₀*Q) (mul_le_mul_of_nonneg_left hQB hr0.le) hη.le
  apply hab.trans
  calc
    _ ≤ 4*L*(K*(q:ℝ)^η)*(r₀^η*B^η)/η := by gcongr
    _ = _ := by dsimp only [L]; rw [Real.mul_rpow hB0.le (Nat.cast_nonneg q)]; ring

end QuaternaryQuadraticForms
