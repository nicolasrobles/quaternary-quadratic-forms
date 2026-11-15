import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Ordered Dirichlet series from cancellation of coefficient sums

The limits below are limits of finite sums in increasing order of the natural
number index.  No unconditional summability is required at the boundary.
-/

noncomputable section

open Finset Filter MeasureTheory Topology Complex Asymptotics

namespace QuaternaryQuadraticForms

/-- The coefficient sum through a real cutoff. -/
def orderedCoeffSum (a : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊X⌋₊, a n

/-- The finite Dirichlet series, summed in increasing modulus order. -/
def orderedDirichletPartial (a : ℕ → ℂ) (s X : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊X⌋₊, (n : ℂ) ^ (-(s : ℂ)) * a n

/-- The Abel integral specifying the ordered boundary value. -/
def orderedDirichletValue (a : ℕ → ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
    orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))

theorem orderedCoeffSum_eq_Icc_one (a : ℕ → ℂ) (ha : a 0 = 0) (X : ℝ) :
    orderedCoeffSum a X = ∑ n ∈ Icc 1 ⌊X⌋₊, a n := by
  rw [orderedCoeffSum, ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊X⌋₊),
    sum_insert (by aesop), ha, zero_add, zero_add]

theorem orderedDirichletPartial_four (a : ℕ → ℂ) (ha : a 0 = 0) (X : ℝ) :
    orderedDirichletPartial a 4 X = ∑ n ∈ Icc 1 ⌊X⌋₊, a n / (n : ℂ) ^ 4 := by
  rw [orderedDirichletPartial, ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊X⌋₊),
    sum_insert (by aesop), ha, mul_zero, zero_add, zero_add]
  apply sum_congr rfl
  intro n _
  rw [Complex.ofReal_ofNat, Complex.cpow_neg, Complex.cpow_ofNat]
  ring

theorem norm_orderedDirichlet_integrand_le
    (a : ℕ → ℂ) {K η s t : ℝ}
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η))
    (ht : 1 ≤ t) :
    ‖orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤
      K * t ^ (2 + η - s) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
  calc
    _ ≤ (K * t ^ (3 + η)) * t ^ (-(s + 1)) := by
      gcongr
      exact hbound t ht
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add htpos]
      congr 2
      ring

theorem orderedDirichlet_integrable
    (a : ℕ → ℂ) {K η s : ℝ} (hη : η ≤ 1 / 2) (hs : 4 ≤ s)
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η)) :
    IntegrableOn (fun t : ℝ ↦
      orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))) (Set.Ioi 1) := by
  have hloc : LocallyIntegrableOn (fun t : ℝ ↦
      orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))) (Set.Ici 1) := by
    simp only [orderedCoeffSum, mul_comm]
    refine locallyIntegrableOn_mul_sum_Icc a zero_le_one ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
    exact (continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  apply Iff.mp integrableOn_Ici_iff_integrableOn_Ioi
  refine hloc.integrableOn_of_isBigO_atTop (g := fun t : ℝ ↦ t ^ (2 + η - s)) ?_ ?_
  · refine isBigO_iff.mpr ⟨K, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
      (zero_le_one.trans ht) _)] using norm_orderedDirichlet_integrand_le a hbound ht
  · exact integrableAtFilter_rpow_atTop_iff.mpr (by linarith)

theorem orderedDirichlet_integral_norm_le
    (a : ℕ → ℂ) {K η s X : ℝ} (hη : η ≤ 1 / 2) (hs : 4 ≤ s)
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η))
    (hX : 1 ≤ X) :
    ‖∫ t in Set.Ioi X, orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤
      K * X ^ (3 + η - s) / (s - 3 - η) := by
  have he : 2 + η - s < -1 := by linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ ∫ t in Set.Ioi X, K * t ^ (2 + η - s) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt he hXpos).const_mul K)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_orderedDirichlet_integrand_le a hbound (hX.trans ht.le)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt he hXpos]
      rw [show 2 + η - s + 1 = 3 + η - s by ring]
      rw [show 3 + η - s = -(s - 3 - η) by ring, neg_div_neg_eq]
      ring

/-- The Abel integral is the limit of the ordered finite series. -/
theorem tendsto_orderedDirichletPartial
    (a : ℕ → ℂ) (ha : a 0 = 0) {K η s : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hs : 4 ≤ s)
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η)) :
    Tendsto (orderedDirichletPartial a s) atTop (𝓝 (orderedDirichletValue a s)) := by
  have hspos : 0 < s := by linarith
  have hszero : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hr : 0 ≤ 3 + η := by linarith
  have hsr : 3 + η < (s : ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, a k) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (3 + η)) := by
    refine isBigO_iff.mpr ⟨K, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [orderedCoeffSum, Nat.floor_natCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using
      hbound n (Nat.one_le_cast.mpr hn)
  have hOreal : orderedCoeffSum a =O[atTop] (fun t : ℝ ↦ t ^ (3 + η)) := by
    refine isBigO_iff.mpr ⟨K, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (zero_le_one.trans ht) _)] using hbound t ht
  have hdiff (t : ℝ) (ht : t ∈ Set.Ici 1) :
      DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-(s : ℂ))) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne'
      (neg_ne_zero.mpr hszero)
  have hnat : Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, (k : ℂ) ^ (-(s : ℂ)) * a k)
      atTop (𝓝 (orderedDirichletValue a s)) := by
    unfold orderedDirichletValue
    rw [← integral_const_mul]
    convert tendsto_sum_mul_atTop_nhds_one_sub_integral₀
      (f := fun x : ℝ ↦ (x : ℂ) ^ (-(s : ℂ))) (l := 0) a ha hdiff ?_ ?_ ?_
      (integrableAtFilter_rpow_atTop_iff.mpr
        (show (-(s : ℂ) - 1).re + (3 + η) < -1 by
          simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
          linarith)) using 1
    · rw [zero_sub, ← integral_neg]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      dsimp only
      rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (neg_ne_zero.mpr hszero)]
      unfold orderedCoeffSum
      ring_nf
    · refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one ?_)).locallyIntegrableOn
      simpa only [Complex.neg_re, Complex.ofReal_re, neg_lt_zero] using hspos
    · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-((s : ℂ).re - (3 + η))))
          atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (sub_pos.mpr hsr)).comp tendsto_natCast_atTop_atTop
      refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-(s : ℂ).re)
        (3 + η) _ ?_ hO ?_).trans_tendsto hlim
      · exact isBigO_norm_left.mp <| (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
      · linarith
    · refine IsBigO.mul_atTop_rpow_of_isBigO_rpow (-((s : ℂ) + 1).re) (3 + η) _
        ?_ hOreal ?_
      · simpa [-neg_add_rev, neg_add'] using isBigO_deriv_ofReal_cpow_const_atTop (-(s : ℂ))
      · simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.one_re]
        linarith
  exact hnat.comp tendsto_nat_floor_atTop

/-- Finite Abel summation in the normalization used for the ordered series. -/
theorem orderedDirichletPartial_eq_boundary_add_integral
    (a : ℕ → ℂ) (ha : a 0 = 0) {s X : ℝ} (hs : 4 ≤ s) :
    orderedDirichletPartial a s X =
      (X : ℂ) ^ (-(s : ℂ)) * orderedCoeffSum a X +
        (s : ℂ) * ∫ t in Set.Ioc (1 : ℝ) X,
          orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1)) := by
  have hspos : 0 < s := by linarith
  have hszero : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc 1 X) :
      DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-(s : ℂ))) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne'
      (neg_ne_zero.mpr hszero)
  have hint : IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ (-(s : ℂ)))
      (Set.Icc 1 X) := by
    apply IntegrableOn.mono_set _ Set.Icc_subset_Ici_self
    refine Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one ?_)
    simpa only [Complex.neg_re, Complex.ofReal_re, neg_lt_zero] using hspos
  have hab := sum_mul_eq_sub_integral_mul₀ a ha X hdiff hint
  simp only [Complex.ofReal_natCast] at hab
  have hid : (∫ t in Set.Ioc (1 : ℝ) X,
      deriv (fun x : ℝ ↦ (x : ℂ) ^ (-(s : ℂ))) t * ∑ n ∈ Icc 0 ⌊t⌋₊, a n) =
      -(s : ℂ) * ∫ t in Set.Ioc (1 : ℝ) X,
        orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht.1).ne' (neg_ne_zero.mpr hszero)]
    unfold orderedCoeffSum
    ring_nf
  rw [orderedDirichletPartial, hab, hid]
  unfold orderedCoeffSum
  ring

/-- The remainder is the tail Abel integral minus the endpoint term. -/
theorem orderedDirichletValue_sub_partial
    (a : ℕ → ℂ) (ha : a 0 = 0) {K η s X : ℝ}
    (hη : η ≤ 1 / 2) (hs : 4 ≤ s)
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η))
    (hX : 1 ≤ X) :
    orderedDirichletValue a s - orderedDirichletPartial a s X =
      (s : ℂ) * (∫ t in Set.Ioi X,
        orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))) -
      (X : ℂ) ^ (-(s : ℂ)) * orderedCoeffSum a X := by
  have hint := orderedDirichlet_integrable a hη hs hbound
  have hsplit : (∫ t in Set.Ioi (1 : ℝ),
        orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))) =
      (∫ t in Set.Ioc (1 : ℝ) X,
        orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1))) +
      ∫ t in Set.Ioi X,
        orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hX]
    apply setIntegral_union _ measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self)
      (hint.mono_set (Set.Ioi_subset_Ioi hX))
    exact Set.disjoint_left.mpr fun t ht₁ ht₂ ↦ (not_lt_of_ge ht₁.2) ht₂
  rw [orderedDirichletValue, hsplit,
    orderedDirichletPartial_eq_boundary_add_integral a ha hs]
  ring

/-- A tail estimate uniform for every real exponent `s ≥ 4`. -/
theorem norm_orderedDirichletValue_sub_partial_le
    (a : ℕ → ℂ) (ha : a 0 = 0) {K η s X : ℝ}
    (hK : 0 ≤ K) (hη : η ≤ 1 / 2) (hs : 4 ≤ s)
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η))
    (hX : 1 ≤ X) :
    ‖orderedDirichletValue a s - orderedDirichletPartial a s X‖ ≤
      9 * K * X ^ (-1 + η) := by
  have hspos : 0 < s := by linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hden : 0 < s - 3 - η := by linarith
  have hratio : s / (s - 3 - η) ≤ 8 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hboundary : ‖(X : ℂ) ^ (-(s : ℂ)) * orderedCoeffSum a X‖ ≤
      K * X ^ (3 + η - s) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    calc
      _ ≤ X ^ (-s) * (K * X ^ (3 + η)) := by
        gcongr
        exact hbound X hX
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hXpos]
        congr 2
        ring
  rw [orderedDirichletValue_sub_partial a ha hη hs hbound hX]
  calc
    _ ≤ ‖(s : ℂ) * (∫ t in Set.Ioi X,
          orderedCoeffSum a t * (t : ℂ) ^ (-((s : ℂ) + 1)))‖ +
        ‖(X : ℂ) ^ (-(s : ℂ)) * orderedCoeffSum a X‖ := norm_sub_le _ _
    _ ≤ s * (K * X ^ (3 + η - s) / (s - 3 - η)) +
        K * X ^ (3 + η - s) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      gcongr
      exact orderedDirichlet_integral_norm_le a hη hs hbound hX
    _ = (s / (s - 3 - η) + 1) * K * X ^ (3 + η - s) := by ring
    _ ≤ 9 * K * X ^ (3 + η - s) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
      exact mul_le_mul_of_nonneg_right (by linarith) hK
    _ ≤ 9 * K * X ^ (-1 + η) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by positivity)

/-- The ordered Abel integral is continuous from the right at exponent four. -/
theorem continuousWithinAt_orderedDirichletValue_four
    (a : ℕ → ℂ) {K η : ℝ} (hK : 0 ≤ K) (hη : η ≤ 1 / 2)
    (hbound : ∀ v : ℝ, 1 ≤ v → ‖orderedCoeffSum a v‖ ≤ K * v ^ (3 + η)) :
    ContinuousWithinAt (orderedDirichletValue a) (Set.Ici 4) 4 := by
  unfold orderedDirichletValue
  apply Complex.continuous_ofReal.continuousWithinAt.mul
  apply continuousWithinAt_of_dominated (bound := fun t : ℝ ↦ K * t ^ (-2 + η))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (orderedDirichlet_integrable a hη hs hbound).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      _ ≤ K * t ^ (2 + η - s) :=
        norm_orderedDirichlet_integrand_le a hbound ht.le
      _ ≤ K * t ^ (-2 + η) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht.le (by change 4 ≤ s at hs; linarith)) hK
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith : -2 + η < -1) zero_lt_one).const_mul K
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply continuousWithinAt_const.mul
    exact ((Complex.continuous_ofReal.continuousWithinAt.add continuousWithinAt_const).neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'))

end QuaternaryQuadraticForms
