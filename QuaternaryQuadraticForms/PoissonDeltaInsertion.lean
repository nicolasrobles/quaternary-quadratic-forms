import QuaternaryQuadraticForms.PoissonDeltaArithmetic

/-!
# Delta insertion into the weighted lattice sum

All exchanges are justified by the finite set of integer points in the
scaled weight support and the existing finite-support delta-symbol theorem.
No Poisson summation input is used in this part of the proof.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- For each integer point the positive-modulus series is summable. -/
theorem poissonDeltaLatticeTerm_summable
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (hQ : 3 ≤ B / Real.sqrt (q : ℝ)) (w : RealVector4 → ℂ)
    (x : Fin 4 → ℤ) :
    Summable (fun c : ℕ+ =>
      poissonDeltaLatticeTerm ξ q A B (B / Real.sqrt (q : ℝ)) w c x) := by
  by_cases hdiv : (q : ℤ) ∣ integralQuadraticValue A x
  · obtain ⟨n, hn⟩ := hdiv
    simp_rw [poissonDeltaLatticeTerm_eq_of_dvd ξ q A B hB w _ x n hn]
    exact (deltaSymbolTerm_summable heathBrownDeltaKernel
      heathBrownDeltaKernel_properties.2.2 _ (by linarith) n).mul_left _
  · simp only [poissonDeltaLatticeTerm_eq_zero_of_not_dvd ξ q A B
      (B / Real.sqrt (q : ℝ)) w _ x hdiv]
    exact summable_zero

/-- The delta identity at a single integer point, including points off the
cone congruence and the origin. -/
theorem weightedQuadraticZeroSum_pointwise_delta
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (hQ : 3 ≤ B / Real.sqrt (q : ℝ)) (w : RealVector4 → ℂ)
    (x : Fin 4 → ℤ) :
    (if integralQuadraticValue A x = 0 then
      w (B⁻¹ • integerRealVector x) * compositeWeight ξ q x else 0) =
      ((heathBrownNormalization (B / Real.sqrt (q : ℝ)) /
        (B / Real.sqrt (q : ℝ)) ^ 2 : ℝ) : ℂ) *
        ∑' c : ℕ+, poissonDeltaLatticeTerm ξ q A B
          (B / Real.sqrt (q : ℝ)) w c x := by
  by_cases hdiv : (q : ℤ) ∣ integralQuadraticValue A x
  · obtain ⟨n, hn⟩ := hdiv
    have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
    have hz : integralQuadraticValue A x = 0 ↔ n = 0 := by
      rw [hn, mul_eq_zero]
      simp only [hq, false_or]
    simp only [hz]
    simp_rw [poissonDeltaLatticeTerm_eq_of_dvd ξ q A B hB w _ x n hn]
    rw [tsum_mul_left]
    calc
      _ = (w (B⁻¹ • integerRealVector x) * compositeWeight ξ q x) *
          (if n = 0 then 1 else 0 : ℂ) := by
        by_cases hn0 : n = 0 <;> simp [hn0]
      _ = _ := by
        rw [heathBrown_delta_identity _ hQ n]
        ring
  · have hF : integralQuadraticValue A x ≠ 0 := by
      intro hx
      exact hdiv (hx ▸ dvd_zero (q : ℤ))
    simp only [if_neg hF, poissonDeltaLatticeTerm_eq_zero_of_not_dvd ξ q A B
      (B / Real.sqrt (q : ℝ)) w _ x hdiv, tsum_zero, mul_zero]

/-- A finite common support in the first variable justifies the sum exchange. -/
theorem poisson_tsum_comm_of_finite_left {α β : Type*}
    (f : α → β → ℂ) (s : Finset α)
    (hzero : ∀ a, a ∉ s → ∀ b, f a b = 0)
    (hsum : ∀ a ∈ s, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  classical
  calc
    _ = ∑ a ∈ s, ∑' b, f a b := by
      apply tsum_eq_sum
      intro a ha
      simp only [hzero a ha, tsum_zero]
    _ = ∑' b, ∑ a ∈ s, f a b := (Summable.tsum_finsetSum hsum).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (s := s) (fun a ha => hzero a ha b)).symm

/-- The actual weighted zero sum after delta insertion, with the original
unit-residue summation and the literal compactly supported functions g_c. -/
theorem weightedQuadraticZeroSum_delta
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (hQ : 3 ≤ B / Real.sqrt (q : ℝ)) (w : RealVector4 → ℂ)
    (hw : HasCompactSupport w) :
    weightedQuadraticZeroSum ξ q A B w =
      ((heathBrownNormalization (B / Real.sqrt (q : ℝ)) /
        (B / Real.sqrt (q : ℝ)) ^ 2 : ℝ) : ℂ) *
        ∑' c : ℕ+, ∑ a : (ZMod (c : ℕ))ˣ, ∑' x : Fin 4 → ℤ,
          mixedIntegerSummand ξ q (c : ℕ) A 0
            (((a : ZMod (c : ℕ)).val : ℕ) : ℤ) x *
            poissonTestFunction A B (B / Real.sqrt (q : ℝ)) w c (integerRealVector x) := by
  classical
  let Q := B / Real.sqrt (q : ℝ)
  let coeff : ℂ := ((heathBrownNormalization Q / Q ^ 2 : ℝ) : ℂ)
  let f := fun (x : Fin 4 → ℤ) (c : ℕ+) => poissonDeltaLatticeTerm ξ q A B Q w c x
  have hfin := scaledWeight_integerRealVector_finite w hw B hB
  let s := hfin.toFinset
  have hzero (x : Fin 4 → ℤ) (hx : x ∉ s) : w (B⁻¹ • integerRealVector x) = 0 := by
    simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hx
  have hfzero : ∀ x, x ∉ s → ∀ c, f x c = 0 := by
    intro x hx c
    exact poissonDeltaLatticeTerm_eq_zero_of_weight_eq_zero ξ q A B Q w c x (hzero x hx)
  have hfsum : ∀ x ∈ s, Summable (f x) := by
    intro x _
    exact poissonDeltaLatticeTerm_summable ξ q A B hB hQ w x
  change weightedQuadraticZeroSum ξ q A B w = coeff * _
  calc
    _ = ∑' x : Fin 4 → ℤ, coeff * ∑' c : ℕ+, f x c := by
      apply tsum_congr
      intro x
      exact weightedQuadraticZeroSum_pointwise_delta ξ q A B hB hQ w x
    _ = coeff * ∑' x, ∑' c, f x c := tsum_mul_left
    _ = coeff * ∑' c, ∑' x, f x c := by
      rw [poisson_tsum_comm_of_finite_left f s hfzero hfsum]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro c
      dsimp only [f, poissonDeltaLatticeTerm]
      apply Summable.tsum_finsetSum
      intro a _
      apply summable_of_ne_finset_zero (s := s)
      intro x hx
      simp only [poissonTestFunction, hzero x hx, zero_mul, mul_zero]

end QuaternaryQuadraticForms
