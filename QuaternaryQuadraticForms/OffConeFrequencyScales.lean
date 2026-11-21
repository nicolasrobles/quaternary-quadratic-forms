import QuaternaryQuadraticForms.OffConeFrequencyReduction

/-! # Uniform bounds for the factors in the off-cone modulus sum -/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The growth of the integral dual form at all the off-cone frequencies is
absorbed uniformly into the divisor-epsilon factor in Lemma 3.6. -/
theorem offCone_dual_growth (A : Matrix (Fin 4) (Fin 4) ℤ) (r₀ η : ℝ)
    (hr : 1 ≤ r₀) (hη : 0 < η) (hη' : η ≤ 1/4) :
    ∃ L : ℝ, 0 < L ∧ ∀ (B q : ℝ), 1 ≤ B → 1 ≤ q →
      ∀ u ∈ offConeFrequencies A (Real.sqrt q * B^η),
      (r₀*(B/Real.sqrt q)*|(integralQuadraticValue A.adjugate u : ℝ)|)^η ≤
        L * (B*q)^(2*η) := by
  obtain ⟨M, hM, hform⟩ := dualQuadraticValue_ball_bound A
  refine ⟨(r₀*M)^η, by positivity, ?_⟩
  intro B q hB hq u hu
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hs1 : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
  have hX : r₀*(B/Real.sqrt q) ≤ r₀*B :=
    mul_le_mul_of_nonneg_left (div_le_self hB0.le hs1) (by linarith)
  have hU : (Real.sqrt q * B^η)^2 ≤ q*B := by
    rw [mul_pow, Real.sq_sqrt hq0.le, ← Real.rpow_natCast (B^η) 2, ← Real.rpow_mul hB0.le]
    apply mul_le_mul_of_nonneg_left _ hq0.le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB (show η*2 ≤ 1 by linarith)
  have hf := (hform _ (by positivity) u (mem_offConeFrequencies.mp hu).2.1).trans
    (mul_le_mul_of_nonneg_left hU hM.le)
  calc
    _ ≤ (r₀*B*(M*(q*B)))^η := Real.rpow_le_rpow (by positivity)
      (mul_le_mul hX hf (abs_nonneg _) (by positivity)) hη.le
    _ ≤ ((r₀*M)*(B*q)^2)^η := by
      apply Real.rpow_le_rpow (by positivity) _ hη.le
      calc
        _ = (r₀*M*B^2)*q := by ring
        _ ≤ (r₀*M*B^2)*q^2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        _ = _ := by ring
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast (B*q) 2, ← Real.rpow_mul (by positivity)]; norm_num

/-- The two terms in Lemma 3.11, including the divisibility factor d²,
contribute at most 2 q³ B^(3η) for each factorization q=d e. -/
theorem offCone_average_scale (d e B η : ℝ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hB : 1 ≤ B) (hη : 0 ≤ η) :
    let q := d*e
    let U := Real.sqrt q * B^η
    d^2 * e^(3/2 : ℝ) * (U^3 / d + e^(1/2 : ℝ)*U^2) ≤
      2*q^3 * B^(3*η) := by
  let q := d*e
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have he0 : 0 < e := zero_lt_one.trans_le he
  have hq0 : 0 < q := mul_pos hd0 he0
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hhalf (x : ℝ) (hx : 0 ≤ x) : x^(3/2 : ℝ) = (Real.sqrt x)^3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x^(1/2 : ℝ)) 3, ← Real.rpow_mul hx]
    norm_num
  have he2 : e^(3/2 : ℝ) * e^(1/2 : ℝ) = e^2 := by
    rw [← Real.rpow_add he0]; norm_num
  have hde : d*e^(3/2 : ℝ) ≤ q^(3/2 : ℝ) := by
    rw [show q = d*e from rfl, Real.mul_rpow hd0.le he0.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hd (by norm_num : (1:ℝ) ≤ 3/2))
  have hfirst : d*e^(3/2 : ℝ) * (Real.sqrt q)^3 ≤ q^3 := by
    apply (mul_le_mul_of_nonneg_right hde (by positivity : 0 ≤ (Real.sqrt q)^3)).trans_eq
    rw [hhalf q hq0.le]
    calc (Real.sqrt q)^3 * (Real.sqrt q)^3 = ((Real.sqrt q)^2)^3 := by ring
         _ = _ := by rw [Real.sq_sqrt hq0.le]
  have hb1 : 1 ≤ B^η := Real.one_le_rpow hB hη
  have hb3 : (B^η)^2 ≤ (B^η)^3 := pow_le_pow_right₀ hb1 (by norm_num)
  change d^2 * e^(3/2 : ℝ) * ((Real.sqrt q * B^η)^3 / d +
    e^(1/2 : ℝ)*(Real.sqrt q * B^η)^2) ≤ _
  calc
    _ = (d*e^(3/2 : ℝ)*(Real.sqrt q)^3)*(B^η)^3 +
        (d^2*e^2*q)*(B^η)^2 := by
      rw [mul_pow (Real.sqrt q) (B^η) 2, Real.sq_sqrt hq0.le, ← he2]
      field_simp
    _ ≤ q^3*(B^η)^3 + q^3*(B^η)^3 := by
      apply add_le_add (mul_le_mul_of_nonneg_right hfirst (by positivity))
      have heq : d^2*e^2*q = q^3 := by dsimp [q]; ring
      rw [heq]; exact mul_le_mul_of_nonneg_left hb3 (by positivity)
    _ = _ := by
      rw [mul_comm (3:ℝ) η, Real.rpow_mul hB0.le]
      norm_cast
      dsimp [q]
      ring

end QuaternaryQuadraticForms
