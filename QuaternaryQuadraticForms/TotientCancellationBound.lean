import QuaternaryQuadraticForms.ConeTotientReindex
import QuaternaryQuadraticForms.CoprimeCubicBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Cancellation in the totient-weighted sum with an exact gcd condition

The exact relative-totient rearrangement reduces the actual sum to
coprime cubic sums. Uniform cubic cancellation then leaves one
harmonic sum and one divisor-count factor, with no dependence of the
constant on the arithmetic parameters or cutoff.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ArithmeticFunction.Moebius

/-- Cubic cancellation bounds the literal totient sum with a fixed
gcd by one divisor count and the ordinary harmonic sum. -/
theorem sum_gcd_totient_norm_le_harmonic (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ T : ℕ,
      ‖∑ n ∈ Finset.Icc 1 T, f n * (n : ℂ) ^ 3‖ ≤ B * (T : ℝ) ^ 3)
    (q d e T : ℕ) (hd : 0 < d) (he : e ≠ 0) (hqde : q = d * e) :
    ‖∑ c ∈ gcdModuliUpTo q d T, f c * (c : ℂ) ^ 2 * (c.totient : ℂ)‖ ≤
      B * (e.divisors.card : ℝ) * (T : ℝ) ^ 3 * (harmonic T : ℝ) := by
  classical
  have hprefactor : ‖f d * (d : ℂ) ^ 2 * (d.totient : ℂ)‖ ≤ (d : ℝ) ^ 3 := by
    simp only [norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ 1 * (d : ℝ) ^ 2 * (d : ℝ) := by
        gcongr
        · exact hf d
        · exact_mod_cast Nat.totient_le d
      _ = (d : ℝ) ^ 3 := by ring
  have hterm (h : ℕ) (hh : 0 < h) :
      ‖(f d * (d : ℂ) ^ 2 * (d.totient : ℂ)) *
        ((μ h : ℂ) * f h * (h : ℂ) ^ 2 *
          ∑ k ∈ (Finset.Icc 1 (T / (d * h))).filter (fun k => k.Coprime e),
            f k * (k : ℂ) ^ 3)‖ ≤
      B * (e.divisors.card : ℝ) * (T : ℝ) ^ 3 * (1 / (h : ℝ)) := by
    have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
    have hquotient : (d : ℝ) ^ 3 * (h : ℝ) ^ 2 *
        ((T / (d * h) : ℕ) : ℝ) ^ 3 ≤ (T : ℝ) ^ 3 / (h : ℝ) := by
      apply (le_div_iff₀ hhR).mpr
      calc
        _ = (((d * h) * (T / (d * h)) : ℕ) : ℝ) ^ 3 := by
          push_cast
          ring
        _ ≤ (T : ℝ) ^ 3 := by
          gcongr
          exact_mod_cast Nat.mul_div_le T (d * h)
    rw [norm_mul]
    calc
      _ ≤ (d : ℝ) ^ 3 *
          (1 * 1 * (h : ℝ) ^ 2 *
            (B * (e.divisors.card : ℝ) * ((T / (d * h) : ℕ) : ℝ) ^ 3)) := by
        simp only [norm_mul, norm_pow, Complex.norm_natCast]
        gcongr
        · simpa only [norm_mul, norm_pow, Complex.norm_natCast] using hprefactor
        · exact moebius_complex_norm_le_one h
        · exact hf h
        · exact coprime_cubic_sum_norm_le f hf B hB hbound e (T / (d * h)) he
      _ = (B * (e.divisors.card : ℝ)) *
          ((d : ℝ) ^ 3 * (h : ℝ) ^ 2 * ((T / (d * h) : ℕ) : ℝ) ^ 3) := by ring
      _ ≤ (B * (e.divisors.card : ℝ)) * ((T : ℝ) ^ 3 / (h : ℝ)) :=
        mul_le_mul_of_nonneg_left hquotient (mul_nonneg hB (Nat.cast_nonneg _))
      _ = _ := by ring
  rw [sum_gcd_totient_eq_moebius f q d e T hd hqde, Finset.mul_sum]
  calc
    _ ≤ ∑ h ∈ (Finset.Icc 1 (T / d)).filter (fun h => h.Coprime q),
        ‖(f d * (d : ℂ) ^ 2 * (d.totient : ℂ)) *
          ((μ h : ℂ) * f h * (h : ℂ) ^ 2 *
            ∑ k ∈ (Finset.Icc 1 (T / (d * h))).filter (fun k => k.Coprime e),
              f k * (k : ℂ) ^ 3)‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ (Finset.Icc 1 (T / d)).filter (fun h => h.Coprime q),
        B * (e.divisors.card : ℝ) * (T : ℝ) ^ 3 * (1 / (h : ℝ)) := by
      apply Finset.sum_le_sum
      intro h hh
      exact hterm h (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).1
    _ ≤ ∑ h ∈ Finset.Icc 1 T,
        B * (e.divisors.card : ℝ) * (T : ℝ) ^ 3 * (1 / (h : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro h hh
        obtain ⟨hlower, hupper⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1
        exact Finset.mem_Icc.mpr ⟨hlower, hupper.trans (Nat.div_le_self T d)⟩
      · intro h _ _
        positivity
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]

/-- The same cancellation estimate at a real cutoff at least one,
with the harmonic factor bounded by `1 + log X`. -/
theorem sum_gcd_totient_floor_norm_le_log (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ T : ℕ,
      ‖∑ n ∈ Finset.Icc 1 T, f n * (n : ℂ) ^ 3‖ ≤ B * (T : ℝ) ^ 3)
    (q d e : ℕ) (hd : 0 < d) (he : e ≠ 0) (hqde : q = d * e)
    (X : ℝ) (hX : 1 ≤ X) :
    ‖∑ c ∈ gcdModuliUpTo q d ⌊X⌋₊, f c * (c : ℂ) ^ 2 * (c.totient : ℂ)‖ ≤
      B * (e.divisors.card : ℝ) * X ^ 3 * (1 + Real.log X) := by
  have hXnonneg : 0 ≤ X := zero_le_one.trans hX
  have hharmonic : 0 ≤ (harmonic ⌊X⌋₊ : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  refine (sum_gcd_totient_norm_le_harmonic f hf B hB hbound q d e ⌊X⌋₊ hd he hqde).trans ?_
  calc
    _ ≤ B * (e.divisors.card : ℝ) * X ^ 3 * (harmonic ⌊X⌋₊ : ℝ) := by
      gcongr
      exact Nat.floor_le hXnonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log X hX)
      (mul_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) (pow_nonneg hXnonneg 3))

end QuaternaryQuadraticForms
