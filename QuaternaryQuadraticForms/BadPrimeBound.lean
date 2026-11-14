import QuaternaryQuadraticForms.BadPrimeGaussBound
import QuaternaryQuadraticForms.CompleteSumNorm

/-!
# Complete Lemma 3.3: the uniform complete-sum bound

The actual source sum is bounded at every positive modulus and every integral
frequency. The proof derives the inner Gauss bound from symmetry and integer
nonsingularity and then sums over the actual unit parameters. No condition
on the prime divisors of the modulus is required.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual complete sum is bounded uniformly in the positive modulus and
frequency, with the determinant absolute value written as a natural number. -/
theorem unweightedCompleteSum_norm_le (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (u : Fin 4 → ℤ) :
    ‖unweightedCompleteSum c A u‖ ≤
      4 * Real.sqrt (A.det.natAbs : ℝ) * (c : ℝ) ^ 3 := by
  have h := unweightedCompleteSum_norm_le_of_gauss_bound c A u
    (4 * Real.sqrt (A.det.natAbs : ℝ) * (c : ℝ) ^ 2)
    (fun a => quadraticGaussSum_integral_norm_le c A hA hdet a _)
  calc
    _ ≤ (c : ℝ) * (4 * Real.sqrt (A.det.natAbs : ℝ) * (c : ℝ) ^ 2) := h
    _ = _ := by ring

/-- Lemma 3.3 for the manuscript's actual complete sum: every positive
modulus, every integral frequency, and the exact real constant `4 sqrt(|α|)`. -/
theorem bad_prime_bound (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (u : Fin 4 → ℤ) :
    ‖unweightedCompleteSum c A u‖ ≤
      4 * Real.sqrt |(A.det : ℝ)| * (c : ℝ) ^ 3 := by
  simpa only [Nat.cast_natAbs, Int.cast_abs] using
    unweightedCompleteSum_norm_le c A hA hdet u

end QuaternaryQuadraticForms
