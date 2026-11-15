import QuaternaryQuadraticForms.ModulusSumFactorization
import QuaternaryQuadraticForms.GoodUnweightedCompleteSum
import QuaternaryQuadraticForms.QuadraticCharacterPeriod

/-!
# The actual good-modulus sum on the dual cone

At zero dual value the actual Ramanujan sum equals the Euler totient.
The good-prime restriction is incorporated into the proved periodic
quadratic coefficient, so every later cancellation bound concerns the
actual unweighted complete sums with their original gcd condition.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The exact good-modulus evaluation on the integral dual cone. -/
theorem unweightedCompleteSum_on_dual_cone (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hc : c.Coprime (quadraticBadPrimeModulus A))
    (u : Fin 4 → ℤ) (hu : dotProduct u (A.adjugate.mulVec u) = 0) :
    unweightedCompleteSum c A u =
      globalQuadraticChar A.det c * (c : ℂ) ^ 2 * (Nat.totient c : ℂ) := by
  rw [unweightedCompleteSum_good_modulus c A hA hc u, hu, integralRamanujanSum_zero]

/-- The sum of actual good complete sums is the totient sum twisted by
the actual periodic quadratic coefficient, which vanishes at bad indices. -/
theorem good_modulus_sum_eq_quadratic_totient (q d T : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (u : Fin 4 → ℤ) (hu : dotProduct u (A.adjugate.mulVec u) = 0) :
    (∑ c ∈ (gcdModuliUpTo q d T).filter
        (fun c => c.Coprime (quadraticBadPrimeModulus A)),
      unweightedCompleteSumValue c A u) =
        ∑ c ∈ gcdModuliUpTo q d T,
          goodQuadraticChar A.det c * (c : ℂ) ^ 2 * (Nat.totient c : ℂ) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  letI : NeZero c := ⟨Nat.ne_of_gt ((mem_gcdModuliUpTo q d T c).mp hc).1⟩
  by_cases hgood : c.Coprime (quadraticBadPrimeModulus A)
  · rw [if_pos hgood, unweightedCompleteSumValue_of_neZero,
      unweightedCompleteSum_on_dual_cone c A hA hgood u hu,
      goodQuadraticChar_of_coprime A.det c hgood]
  · rw [if_neg hgood, goodQuadraticChar_of_not_coprime A.det c hgood, zero_mul, zero_mul]

end QuaternaryQuadraticForms
