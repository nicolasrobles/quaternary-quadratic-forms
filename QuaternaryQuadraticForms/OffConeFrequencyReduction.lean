import QuaternaryQuadraticForms.PoissonFrequencyTail
import QuaternaryQuadraticForms.GenericModulusTheorem
import QuaternaryQuadraticForms.SourceAverageFrequencyTheorem

/-! # The bounded off-cone part of the Poisson frequency sum -/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Exactly the frequencies in the second clause of Lemma 5.2. -/
def offConeFrequencies (A : Matrix (Fin 4) (Fin 4) ℤ) (U : ℝ) : Finset (Fin 4 → ℤ) :=
  (divisibleEuclideanBall A 1 U).filter (fun u => integralQuadraticValue A.adjugate u ≠ 0)

theorem mem_offConeFrequencies {A : Matrix (Fin 4) (Fin 4) ℤ} {U : ℝ} {u : Fin 4 → ℤ} :
    u ∈ offConeFrequencies A U ↔ 0 < integerEuclideanNorm u ∧
      integerEuclideanNorm u ≤ U ∧ integralQuadraticValue A.adjugate u ≠ 0 := by
  simp [offConeFrequencies, mem_divisibleEuclideanBall, and_assoc]

/-- All positive c in the strict cutoff occur in their gcd class in the inclusive
modulus sums of Lemma 3.6. Enlarging the cutoff at an integer endpoint is harmless. -/
theorem sourceMixedCompleteSum_sum_le_gcd_classes (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (u : Fin 4 → ℤ) (X : ℝ) :
    ∑ c ∈ poissonModuliBelow X, ‖sourceMixedCompleteSum N ξ q hqN c A u‖ / (c : ℝ)^3 ≤
      ∑ d ∈ q.divisors, modulusNormSum (extendPrimeWeights N ξ) q d A u X := by
  classical
  let f := fun c => normalizedMixedCompleteSum (extendPrimeWeights N ξ) q c A u
  have hinj : Set.InjOn (fun c : ℕ+ => (c : ℕ)) ↑(poissonModuliBelow X) :=
    Subtype.val_injective.injOn
  calc
    _ = ∑ c ∈ (poissonModuliBelow X).image (fun c : ℕ+ => (c : ℕ)), f c := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro c _
      rw [show f (c : ℕ) = _ from normalizedMixedCompleteSum_of_neZero _ q c A u,
        mixedCompleteSum_extend_eq_source N ξ q hqN]
    _ ≤ ∑ c ∈ Finset.Icc 1 ⌊X⌋₊, f c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun c _ _ =>
        normalizedMixedCompleteSum_nonneg _ q c A u)
      intro c hc
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_Icc.mpr ⟨n.pos, Nat.le_floor (mem_poissonModuliBelow.mp hn).le⟩
    _ = _ := (Finset.sum_fiberwise_of_maps_to (g := fun c => Nat.gcd c q)
      (fun c _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right c q, NeZero.ne q⟩) f).symm

/-- The integral dual quadratic polynomial is uniformly O(U²) on the ball. -/
theorem dualQuadraticValue_ball_bound (A : Matrix (Fin 4) (Fin 4) ℤ) :
    ∃ M : ℝ, 0 < M ∧ ∀ U : ℝ, 0 < U → ∀ u : Fin 4 → ℤ, integerEuclideanNorm u ≤ U →
      |(integralQuadraticValue A.adjugate u : ℝ)| ≤ M * U^2 := by
  obtain ⟨M, hM, hb⟩ := realQuadraticValue_abs_bound_closedBall
    (A.adjugate.map (Int.castRingHom ℝ)) 1
  refine ⟨M, hM, ?_⟩
  intro U hU u hu
  have hv : ‖U⁻¹ • integerRealVector u‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hU), ← div_eq_inv_mul]
    exact (div_le_one hU).mpr hu
  have h := hb _ hv
  rw [realQuadraticValue_scaled_integerRealVector, abs_div, abs_of_pos (pow_pos hU 2)] at h
  exact (div_le_iff₀ (pow_pos hU 2)).mp h

/-- The actual sum inside the Poisson prefactor with 0 < ‖u‖ ≤ U and F*(u) ≠ 0. -/
def sourceBoundedOffConeSum (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (w : RealVector4 → ℂ) (X Q U : ℝ) : ℂ :=
  ∑ c ∈ poissonModuliBelow X, ∑ u ∈ offConeFrequencies A U,
    ((c : ℂ)^4)⁻¹ * sourceMixedCompleteSum N ξ q hqN c A u *
      deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w ((c : ℝ)/Q)
        ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u)

/-- Apply (5.5) to every summand and regroup the nonnegative terms by gcd. -/
theorem ScaledFrequencyIntegralBound.offCone_modulus_reduction
    {A : Matrix (Fin 4) (Fin 4) ℤ} {weights : Set (RealVector4 → ℂ)} {η : ℝ}
    (bounds : ScaledFrequencyIntegralBound (realQuadraticValue (A.map (Int.castRingHom ℝ)))
      weights η) :
    ∃ J : ℝ, 0 < J ∧ ∀ (N : ℕ)
      (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
      (q : ℕ) [NeZero q] (hqN : q.Coprime N) (B X : ℝ), 1 ≤ B → ∀ w ∈ weights,
      let U := Real.sqrt q * B^η
      ‖sourceBoundedOffConeSum N ξ q hqN A w X (B/Real.sqrt q) U‖ ≤
        J * q / B * B^(3*η) * (∑ d ∈ q.divisors, ∑ u ∈ offConeFrequencies A U,
          modulusNormSum (extendPrimeWeights N ξ) q d A u X / integerEuclideanNorm u) := by
  obtain ⟨J, hJ, hbound⟩ := bounds
  refine ⟨J, hJ, ?_⟩
  intro N ξ q _ hqN B X hB w hw
  let U := Real.sqrt (q : ℝ) * B^η
  let Q := B / Real.sqrt q
  let L := J * q / B * B^(3*η)
  let f := fun (c : ℕ+) u => ‖sourceMixedCompleteSum N ξ q hqN c A u‖ / (c : ℝ)^3
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hB' : 0 < B := zero_lt_one.trans_le hB
  have hQ : 0 < Q := div_pos hB' (Real.sqrt_pos.mpr (by exact_mod_cast hq1))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  dsimp only
  unfold sourceBoundedOffConeSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ c ∈ poissonModuliBelow X, ∑ u ∈ offConeFrequencies A U,
        L * (f c u / integerEuclideanNorm u) := by
      apply Finset.sum_le_sum
      intro c _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨hp, hU, _⟩ := mem_offConeFrequencies.mp hu
      have hc : 0 < (c : ℝ) := by exact_mod_cast c.pos
      have h1c : 1 ≤ (c : ℝ) := by exact_mod_cast c.pos
      have hI := hbound w hw q hq1 B hB c h1c u hp hU
      dsimp only at hI
      rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      apply (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right
        (mul_nonneg (div_pos hc hQ).le (norm_nonneg _))).trans hI) (by positivity)).trans_eq
      dsimp [L, f]
      field_simp
    _ = L * ∑ u ∈ offConeFrequencies A U, (∑ c ∈ poissonModuliBelow X, f c u) /
        integerEuclideanNorm u := by rw [Finset.sum_comm, Finset.mul_sum]; simp_rw [Finset.sum_div, Finset.mul_sum]
    _ ≤ L * ∑ u ∈ offConeFrequencies A U, (∑ d ∈ q.divisors,
        modulusNormSum (extendPrimeWeights N ξ) q d A u X) / integerEuclideanNorm u := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro u _
      exact div_le_div_of_nonneg_right
        (sourceMixedCompleteSum_sum_le_gcd_classes N ξ q hqN A u X) (integerEuclideanNorm_nonneg u)
    _ = _ := by simp_rw [Finset.sum_div]; rw [Finset.sum_comm]

end QuaternaryQuadraticForms
