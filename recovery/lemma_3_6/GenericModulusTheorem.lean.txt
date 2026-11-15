import QuaternaryQuadraticForms.GenericModulusBound
import QuaternaryQuadraticForms.DivisorPowerBound
import QuaternaryQuadraticForms.LogPowerBound
import QuaternaryQuadraticForms.SourceGoodModulus

/-!
# Complete Lemma 3.6 with a uniform source constant

The actual absolute modulus sum satisfies the manuscript's estimate.
The positive constant is chosen before every modulus, prime-weight
family, frequency, and real cutoff; it depends only on the fixed matrix
and the positive exponent. The stronger intermediate divisor/logarithm
bound uses one divisor-count factor, so separate power bounds in the
cutoff and the absolute dual value give exactly the stated product power.

The source wrapper uses only the original local functions at primes
outside `N`. Its radical condition supplies coprimality with the actual
bad-prime modulus. No character, cone, or asymptotic estimate is assumed.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The full nonzero-dual modulus estimate, with a positive constant
depending only on the fixed matrix and exponent. All varying arithmetic
data and local functions occur after the existential constant. -/
theorem modulusNormSum_le_rpow
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ)
        (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e],
        Squarefree q → q = d * e → q.Coprime (quadraticBadPrimeModulus A) →
        PrimeWeightsInvariant ξ q →
        (∀ p ∈ q.primeFactors, ∀ x : Fin 4 → ZMod p, ‖ξ p x‖ ≤ 1) →
        ∀ (u : Fin 4 → ℤ), dotProduct u (A.adjugate.mulVec u) ≠ 0 →
        ∀ (X : ℝ), 1 ≤ X →
          modulusNormSum ξ q d A u X ≤
            C * ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2 *
              (if (d : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) then 1 else 0) *
                (X * ((dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ)) ^ ε := by
  classical
  let k := (quadraticBadPrimeModulus A).primeFactors.card
  let B : ℝ := 4 * Real.sqrt (A.det.natAbs : ℝ) * (1 + (Real.log 2)⁻¹) ^ k
  have hdetpos : (0 : ℝ) < A.det.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hdet
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨D, hD, hDbound⟩ := divisors_card_le_rpow ε hε
  obtain ⟨L, hL, hLbound⟩ := one_add_log_pow_le_rpow (k + 1) ε hε
  refine ⟨B * D * L, mul_pos (mul_pos hB hD) hL, ?_⟩
  intro ξ q d e _ _ _ hq hqde hqA hξ hξnorm u hu X hX
  by_cases hdu : (d : ℤ) ∣ dotProduct u (A.adjugate.mulVec u)
  · rw [if_pos hdu, mul_one]
    have hM : 0 < (dotProduct u (A.adjugate.mulVec u)).natAbs :=
      Int.natAbs_pos.mpr hu
    have hlog : 0 ≤ 1 + Real.log X :=
      add_nonneg zero_le_one (Real.log_nonneg hX)
    have hXnonneg : 0 ≤ X := zero_le_one.trans hX
    calc
      _ ≤ B * ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2 *
          ((dotProduct u (A.adjugate.mulVec u)).natAbs.divisors.card : ℝ) *
            (1 + Real.log X) ^ (k + 1) :=
        modulusNormSum_le_divisor_log ξ q d e hq hqde A hA hdet
          hqA hξ hξnorm u hu X hX
      _ ≤ B * ‖constrainedFourierSum ξ e A u‖ * (d : ℝ) ^ 2 *
          (D * ((dotProduct u (A.adjugate.mulVec u)).natAbs : ℝ) ^ ε) *
            (L * X ^ ε) := by
        gcongr
        · exact hDbound _ hM
        · exact hLbound X hX
      _ = _ := by
        rw [Real.mul_rpow hXnonneg (Nat.cast_nonneg _)]
        ring
  · rw [modulusNormSum_eq_zero_of_not_dvd ξ q d hq A hA hqA hξ u X hdu,
      if_neg hdu, mul_zero, zero_mul]

/-- Lemma 3.6 for the source's original family of local functions.
The same constant works for every excluded-prime modulus `N`, every
admissible squarefree factorization `q = d * e`, every nonzero integral
dual value, and every real cutoff at least one. -/
theorem source_generic_modulus_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ)
        (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
        (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e],
        Squarefree q → q = d * e → q.Coprime N →
        primeRadical (quadraticBadPrimeModulus A) ∣ N →
        (∀ p (hp : p.Prime) (hN : ¬p ∣ N), ∀ r : ZMod p, r ≠ 0 →
          ∀ y : Fin 4 → ZMod p, ξ p hp hN (r • y) = ξ p hp hN y) →
        (∀ p (hp : p.Prime) (hN : ¬p ∣ N),
          ∀ x : Fin 4 → ZMod p, ‖ξ p hp hN x‖ ≤ 1) →
        ∀ (u : Fin 4 → ℤ), dotProduct u (A.adjugate.mulVec u) ≠ 0 →
        ∀ (X : ℝ), 1 ≤ X →
          modulusNormSum (extendPrimeWeights N ξ) q d A u X ≤
            C * ‖constrainedFourierSum (extendPrimeWeights N ξ) e A u‖ * (d : ℝ) ^ 2 *
              (if (d : ℤ) ∣ dotProduct u (A.adjugate.mulVec u) then 1 else 0) *
                (X * |((dotProduct u (A.adjugate.mulVec u) : ℤ) : ℝ)|) ^ ε := by
  classical
  obtain ⟨C, hC, hbound⟩ := modulusNormSum_le_rpow A hA hdet ε hε
  refine ⟨C, hC, ?_⟩
  intro N ξ q d e _ _ _ hq hqde hqN hrad hξ hξnorm u hu X hX
  have h := hbound (extendPrimeWeights N ξ) q d e hq hqde
    (source_coprime_quadraticBadPrimeModulus N q A hdet hrad hqN)
    (primeWeightsInvariant_extend N q ξ hqN hξ)
    (primeWeightsNorm_le_extend N q ξ hqN hξnorm) u hu X hX
  simpa only [Int.cast_natAbs, Int.cast_abs] using h

end QuaternaryQuadraticForms
