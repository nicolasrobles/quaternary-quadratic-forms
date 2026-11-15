import QuaternaryQuadraticForms.ConeModulusBound
import QuaternaryQuadraticForms.DivisorPowerBound
import QuaternaryQuadraticForms.LogPowerBound

/-!
# Complete Lemma 3.7 with a uniform source constant

For the actual unweighted complete sums on the integral dual cone,
the positive constant is chosen after the fixed form and exponent,
before every modulus, frequency, and real cutoff. The core estimate
in fact holds for every positive factorization `q=d*e`; the source
wrapper retains the manuscript's squarefree hypothesis.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The complete dual-cone cancellation bound, uniform over all positive
factorizations, cone frequencies, and real cutoffs. -/
theorem unweightedModulusSum_le_rpow
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e],
        q = d * e → q.Coprime (quadraticBadPrimeModulus A) →
        ∀ (u : Fin 4 → ℤ), dotProduct u (A.adjugate.mulVec u) = 0 →
        ∀ (X : ℝ), 1 ≤ X →
          ‖unweightedModulusSum q d A u X‖ ≤ C * X ^ 3 * (X * (q : ℝ)) ^ ε := by
  classical
  let r := (quadraticBadPrimeModulus A).primeFactors.card
  let K : ℝ := 4 * Real.sqrt (A.det.natAbs : ℝ) *
    (2 * ((4 * A.det.natAbs : ℕ) : ℝ)) * (1 + (Real.log 2)⁻¹) ^ r
  have hdetpos : (0 : ℝ) < A.det.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hdet
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨D, hD, hDbound⟩ := divisors_card_le_rpow ε hε
  obtain ⟨L, hL, hLbound⟩ := one_add_log_pow_le_rpow (r + 1) ε hε
  refine ⟨K * D * L, mul_pos (mul_pos hK hD) hL, ?_⟩
  intro q d e _ _ _ hqde hqN u hu X hX
  have heq : e ∣ q := hqde ▸ dvd_mul_left e d
  have hdiv : (e.divisors.card : ℝ) ≤ D * (q : ℝ) ^ ε :=
    (Nat.cast_le.mpr (Finset.card_le_card
      (Nat.divisors_subset_of_dvd (NeZero.ne q) heq))).trans
        (hDbound q (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hlog : 0 ≤ 1 + Real.log X := add_nonneg zero_le_one (Real.log_nonneg hX)
  calc
    _ ≤ K * (e.divisors.card : ℝ) * X ^ 3 * (1 + Real.log X) ^ (r + 1) :=
      unweightedModulusSum_le_divisor_log q d e
        (Nat.pos_of_ne_zero (NeZero.ne d)) (NeZero.ne e) hqde
          A hA hdet hns hqN u hu X hX
    _ ≤ K * (D * (q : ℝ) ^ ε) * X ^ 3 * (L * X ^ ε) := by
      gcongr
      exact hLbound X hX
    _ = _ := by
      rw [Real.mul_rpow hX0 (Nat.cast_nonneg q)]
      ring

/-- Lemma 3.7 for the original unweighted complete sums, including the
source's squarefree factorization and every real cutoff at least one. -/
theorem source_cone_modulus_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q d e : ℕ) [NeZero q] [NeZero d] [NeZero e],
        Squarefree q → q = d * e → q.Coprime (quadraticBadPrimeModulus A) →
        ∀ (u : Fin 4 → ℤ), dotProduct u (A.adjugate.mulVec u) = 0 →
        ∀ (X : ℝ), 1 ≤ X →
          ‖unweightedModulusSum q d A u X‖ ≤ C * X ^ 3 * (X * (q : ℝ)) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := unweightedModulusSum_le_rpow A hA hdet hns ε hε
  refine ⟨C, hC, ?_⟩
  intro q d e _ _ _ _hq hqde hqN u hu X hX
  exact hbound q d e hqde hqN u hu X hX

end QuaternaryQuadraticForms
