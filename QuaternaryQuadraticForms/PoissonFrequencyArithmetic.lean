import QuaternaryQuadraticForms.PoissonTheorem
import QuaternaryQuadraticForms.GoodGlobalTheorem
import QuaternaryQuadraticForms.SourceFourierSums
import QuaternaryQuadraticForms.MixedSumNormBounds

/-! # The complete sums in the off-cone and zero-frequency estimates -/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The trivial complete-sum estimate in the large-frequency tail of Lemma 5.2. -/
theorem sourceMixedCompleteSum_trivial_bound (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p hp hN x, ‖ξ p hp hN x‖ ≤ 1)
    (q c : ℕ) [NeZero q] [NeZero c] (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    ‖sourceMixedCompleteSum N ξ q hqN c A u‖ ≤ (q : ℝ)^4 * (c : ℝ)^5 := by
  have hw (x : Fin 4 → ℤ) : ‖sourceCompositeWeight N ξ q hqN x‖ ≤ 1 := by
    rw [← compositeWeight_extend_eq_source]
    exact compositeWeight_norm_le _ q (primeWeightsNorm_le_extend N q ξ hqN hξ) x
  unfold sourceMixedCompleteSum
  calc
    _ ≤ ∑ _a : (ZMod c)ˣ, ∑ _z : Fin 4 → ZMod (q*c), (1 : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro z _
      split_ifs <;> simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one,
        norm_zero, zero_le_one, hw]
    _ = (Fintype.card (ZMod c)ˣ : ℝ) * ((q : ℝ) * c)^4 := by
      simp [ZMod.card]
    _ ≤ (c : ℝ) * ((q : ℝ) * c)^4 := by
      gcongr
      exact_mod_cast zmod_card_units_le c
    _ = _ := by ring

/-- The composite source weight vanishes at the origin for every modulus greater than one. -/
theorem sourceCompositeWeight_zero_of_one_lt (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p hp hN, ξ p hp hN 0 = 0) (n : ℕ) (hn : 1 < n) (hN : n.Coprime N) :
    sourceCompositeWeight N ξ n hN 0 = 0 := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : n.primeFactors))
  simpa using hξ p (Nat.prime_of_mem_primeFactors hp) _

/-- The zero-frequency mixed sum in Lemma 5.4, including the coprime case q=1. -/
theorem sourceMixedCompleteSum_zero_frequency (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p hp hN, ∀ r : ZMod p, r ≠ 0 → ∀ y, ξ p hp hN (r • y) = ξ p hp hN y)
    (hzero : ∀ p hp hN, ξ p hp hN 0 = 0)
    (q c : ℕ) [NeZero q] [NeZero c] (hq : Squarefree q) (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N) :
    sourceMixedCompleteSum N ξ q hqN c A 0 =
      if q.Coprime c then sourceConstrainedFourierSum N ξ q hqN A 0 *
        unweightedCompleteSum c A 0 else 0 := by
  rw [← mixedCompleteSum_extend_eq_source]
  have hcone := mixedCompleteSum_dual_cone (extendPrimeWeights N ξ) q c hq A hA
    (source_coprime_quadraticBadPrimeModulus N q A hdet hrad hqN)
    (primeWeightsInvariant_extend N q ξ hqN hξ) 0 (by simp)
  by_cases h : q.Coprime c
  · rw [if_pos h]
    simpa [h.gcd_eq_one, constrainedFourierSum_extend_eq_source N ξ q hqN] using hcone
  · have hd : 1 < q.gcd c := by
      have hpos := Nat.gcd_pos_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne q))
      have hne : q.gcd c ≠ 1 := h
      omega
    have hw := sourceCompositeWeight_zero_of_one_lt N ξ hzero _ hd
      (hqN.of_dvd_left (Nat.gcd_dvd_left q c))
    rw [← compositeWeight_extend_eq_source] at hw
    rw [if_neg h]
    simpa [hw] using hcone

/-- Equation (5.7) for the literal zero-frequency portion of the truncated Poisson sum. -/
theorem source_zero_frequency_contribution (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hξ : ∀ p hp hN, ∀ r : ZMod p, r ≠ 0 → ∀ y, ξ p hp hN (r • y) = ξ p hp hN y)
    (hzero : ∀ p hp hN, ξ p hp hN 0 = 0)
    (q : ℕ) [NeZero q] (hq : Squarefree q) (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (hrad : primeRadical (quadraticBadPrimeModulus A) ∣ N)
    (w : RealVector4 → ℂ) (B r₀ : ℝ) :
    let Q := B / Real.sqrt q
    let F := realQuadraticValue (A.map (Int.castRingHom ℝ))
    let prefactor : ℂ := (heathBrownNormalization Q * B^2 / (q : ℝ)^3 : ℝ)
    prefactor * (∑' c : ℕ+, if (c : ℝ) < r₀ * Q then
      ((c : ℂ)^4)⁻¹ * sourceMixedCompleteSum N ξ q hqN c A 0 *
        deltaIntegral F w ((c : ℝ) / Q) 0 else 0) =
    prefactor * sourceConstrainedFourierSum N ξ q hqN A 0 *
      ∑' c : ℕ+, if (c : ℝ) < r₀ * Q ∧ q.Coprime c then
        ((c : ℂ)^4)⁻¹ * unweightedCompleteSum c A 0 *
          deltaIntegral F w ((c : ℝ) / Q) 0 else 0 := by
  dsimp only
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro c
  rw [sourceMixedCompleteSum_zero_frequency N ξ hξ hzero q c hq hqN A hA hdet hrad]
  by_cases hr : (c : ℝ) < r₀ * (B / Real.sqrt q) <;> by_cases hp : q.Coprime c <;>
    simp [hr, hp, mul_left_comm, mul_comm, mul_assoc]

end QuaternaryQuadraticForms
