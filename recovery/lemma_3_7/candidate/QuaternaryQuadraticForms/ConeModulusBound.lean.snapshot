import QuaternaryQuadraticForms.ConeModulusFormula
import QuaternaryQuadraticForms.QuadraticCharacterNonprincipal
import QuaternaryQuadraticForms.CharacterCubicBound
import QuaternaryQuadraticForms.TotientCancellationBound
import QuaternaryQuadraticForms.BadPrimeBound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Cancellation of actual unweighted complete sums on the dual cone

The actual quadratic coefficient has zero mean over period `4*|det A|`.
The totient divisor rearrangement supplies good-modulus cancellation.
Exact CRT factorization then permits the bad-supported factor to be
summed outside each good-modulus sum, with its cubic growth canceled
by the divided cutoff. All constants are independent of the frequency,
factorization of `q`, and cutoff.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual good-modulus sum on the dual cone has the harmonic
cancellation bound, with the fixed period derived from the determinant. -/
theorem good_modulus_sum_norm_le_harmonic (q d e T : ℕ)
    (hd : 0 < d) (he : e ≠ 0) (hqde : q = d * e)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (u : Fin 4 → ℤ) (hu : dotProduct u (A.adjugate.mulVec u) = 0) :
    ‖∑ c ∈ (gcdModuliUpTo q d T).filter
        (fun c => c.Coprime (quadraticBadPrimeModulus A)),
      unweightedCompleteSumValue c A u‖ ≤
        (2 * ((4 * A.det.natAbs : ℕ) : ℝ)) * (e.divisors.card : ℝ) *
          (T : ℝ) ^ 3 * (harmonic T : ℝ) := by
  rw [good_modulus_sum_eq_quadratic_totient q d T A hA u hu]
  have hP : 0 < 4 * A.det.natAbs :=
    Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hdet)
  exact sum_gcd_totient_norm_le_harmonic (goodQuadraticCharHom A.det)
    (goodQuadraticChar_norm_le_one A.det) _ (by positivity)
    (periodic_cubic_sum_norm_le (goodQuadraticChar A.det) (4 * A.det.natAbs) hP
      (goodQuadraticChar_periodic A.det)
      (goodQuadraticChar_sum_period_eq_zero A.det hdet hns)
      (goodQuadraticChar_norm_le_one A.det)) q d e T hd he hqde

private theorem harmonic_real_mono (m n : ℕ) (hmn : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hjpos, hjle⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hjpos, hjle.trans hmn⟩
  · intro j _ _
    positivity

/-- The actual dual-cone modulus sum satisfies the uniform finite
divisor/logarithm estimate before absorption into positive powers. -/
theorem unweightedModulusSum_le_divisor_log (q d e : ℕ)
    (hd : 0 < d) (he : e ≠ 0) (hqde : q = d * e)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (hns : ¬IsSquare A.det)
    (hqN : q.Coprime (quadraticBadPrimeModulus A))
    (u : Fin 4 → ℤ) (hu : dotProduct u (A.adjugate.mulVec u) = 0)
    (X : ℝ) (hX : 1 ≤ X) :
    ‖unweightedModulusSum q d A u X‖ ≤
      4 * Real.sqrt (A.det.natAbs : ℝ) *
        (2 * ((4 * A.det.natAbs : ℕ) : ℝ)) *
          (1 + (Real.log 2)⁻¹) ^ (quadraticBadPrimeModulus A).primeFactors.card *
            (e.divisors.card : ℝ) * X ^ 3 *
              (1 + Real.log X) ^ ((quadraticBadPrimeModulus A).primeFactors.card + 1) := by
  classical
  let C₀ : ℝ := 4 * Real.sqrt (A.det.natAbs : ℝ)
  let B : ℝ := 2 * ((4 * A.det.natAbs : ℕ) : ℝ)
  let r := (quadraticBadPrimeModulus A).primeFactors.card
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hlog : 0 ≤ 1 + Real.log X := add_nonneg zero_le_one (Real.log_nonneg hX)
  have hN : quadraticBadPrimeModulus A ≠ 0 :=
    mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hdet)
  have hharm (b : ℕ) : (harmonic (⌊X⌋₊ / b) : ℝ) ≤ 1 + Real.log X :=
    (harmonic_real_mono (⌊X⌋₊ / b) ⌊X⌋₊ (Nat.div_le_self _ _)).trans
      (harmonic_floor_le_one_add_log X hX)
  have hterm (b : ℕ) (hb : b ∈ primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊) :
      ‖unweightedCompleteSumValue b A u *
        ∑ g ∈ (gcdModuliUpTo q d (⌊X⌋₊ / b)).filter
          (fun g => g.Coprime (quadraticBadPrimeModulus A)),
            unweightedCompleteSumValue g A u‖ ≤
        C₀ * B * (e.divisors.card : ℝ) * X ^ 3 * (1 + Real.log X) := by
    have hbpos := ((mem_primeSupportModuliUpTo
      (quadraticBadPrimeModulus A) ⌊X⌋₊ b).mp hb).1
    letI : NeZero b := ⟨Nat.ne_of_gt hbpos⟩
    have hbad : ‖unweightedCompleteSumValue b A u‖ ≤ C₀ * (b : ℝ) ^ 3 := by
      rw [unweightedCompleteSumValue_of_neZero]
      exact unweightedCompleteSum_norm_le b A hA hdet u
    have hgood := good_modulus_sum_norm_le_harmonic q d e (⌊X⌋₊ / b)
      hd he hqde A hA hdet hns u hu
    calc
      _ = ‖unweightedCompleteSumValue b A u‖ *
          ‖∑ g ∈ (gcdModuliUpTo q d (⌊X⌋₊ / b)).filter
            (fun g => g.Coprime (quadraticBadPrimeModulus A)),
              unweightedCompleteSumValue g A u‖ := norm_mul _ _
      _ ≤ (C₀ * (b : ℝ) ^ 3) *
          (B * (e.divisors.card : ℝ) * ((⌊X⌋₊ / b : ℕ) : ℝ) ^ 3 *
            (harmonic (⌊X⌋₊ / b) : ℝ)) :=
        mul_le_mul hbad hgood (norm_nonneg _) (by positivity)
      _ ≤ (C₀ * (b : ℝ) ^ 3) *
          (B * (e.divisors.card : ℝ) * ((⌊X⌋₊ / b : ℕ) : ℝ) ^ 3 *
            (1 + Real.log X)) := by
        gcongr
        exact hharm b
      _ = C₀ * B * (e.divisors.card : ℝ) *
          ((b * (⌊X⌋₊ / b) : ℕ) : ℝ) ^ 3 * (1 + Real.log X) := by
        push_cast
        ring
      _ ≤ _ := by
        gcongr
        exact (Nat.cast_le.mpr (Nat.mul_div_le ⌊X⌋₊ b)).trans (Nat.floor_le hX0)
  rw [unweightedModulusSum_prime_split q d A u hqN X]
  calc
    _ ≤ ∑ b ∈ primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊,
        ‖unweightedCompleteSumValue b A u *
          ∑ g ∈ (gcdModuliUpTo q d (⌊X⌋₊ / b)).filter
            (fun g => g.Coprime (quadraticBadPrimeModulus A)),
              unweightedCompleteSumValue g A u‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊,
        C₀ * B * (e.divisors.card : ℝ) * X ^ 3 * (1 + Real.log X) :=
      Finset.sum_le_sum hterm
    _ = ((primeSupportModuliUpTo (quadraticBadPrimeModulus A) ⌊X⌋₊).card : ℝ) *
        (C₀ * B * (e.divisors.card : ℝ) * X ^ 3 * (1 + Real.log X)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((1 + (Real.log 2)⁻¹) ^ r * (1 + Real.log X) ^ r) *
        (C₀ * B * (e.divisors.card : ℝ) * X ^ 3 * (1 + Real.log X)) :=
      mul_le_mul_of_nonneg_right
        (primeSupportModuliUpTo_card_le_log_normalized (quadraticBadPrimeModulus A) hN X hX)
        (by positivity)
    _ = _ := by
      dsimp only [C₀, B, r]
      rw [pow_succ]
      ring

end QuaternaryQuadraticForms
