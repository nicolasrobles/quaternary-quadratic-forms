import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cubic cancellation with a coprimality condition

Finite Möbius detection and the exact reindexing of positive multiples
transfer a cubic cancellation estimate to coprime indices. The loss is
the actual positive-divisor count of the excluded-prime modulus.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ArithmeticFunction.Moebius

/-- Positive multiples of `d` in a finite interval are exactly `d*k`
with a positive quotient at most the divided cutoff. -/
theorem sum_Icc_dvd_eq_sum_div (d T : ℕ) (hd : 0 < d) (g : ℕ → ℂ) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => d ∣ n), g n) =
      ∑ k ∈ Finset.Icc 1 (T / d), g (d * k) := by
  classical
  apply Finset.sum_bij (fun n _ => n / d)
  · intro n hn
    obtain ⟨hnT, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnle⟩ := Finset.mem_Icc.mp hnT
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnpos hdn) hd,
      Nat.div_le_div_right hnle⟩
  · intro n hn m hm hnm
    have hdn := (Finset.mem_filter.mp hn).2
    have hdm := (Finset.mem_filter.mp hm).2
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
      _ = d * (m / d) := congrArg (fun k => d * k) hnm
      _ = m := Nat.mul_div_cancel' hdm
  · intro k hk
    obtain ⟨hkpos, hkle⟩ := Finset.mem_Icc.mp hk
    refine ⟨d * k, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hkpos, ?_⟩, dvd_mul_right d k⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkle
    · simp [hd.ne']
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- The literal Möbius divisor sum detects coprimality with a positive modulus. -/
theorem coprime_indicator_eq_moebius_sum (n M : ℕ) (hM : M ≠ 0) :
    (if n.Coprime M then (1 : ℂ) else 0) =
      ∑ d ∈ M.divisors, if d ∣ n then (μ d : ℂ) else 0 := by
  classical
  have hg : n.gcd M ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hM))
  have hset : M.divisors.filter (fun d => d ∣ n) = (n.gcd M).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdM, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdM, hg⟩
    · rintro ⟨hdg, _⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_right n M), hM⟩,
        hdg.trans (Nat.gcd_dvd_left n M)⟩
  rw [← Finset.sum_filter, hset]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (n.gcd M))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  dsimp only at h
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply,
    Nat.Coprime] using h.symm

/-- Möbius detection followed by exact finite reindexing of multiples. -/
theorem sum_coprime_eq_sum_moebius_multiples (g : ℕ → ℂ) (M T : ℕ)
    (hM : M ≠ 0) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => n.Coprime M), g n) =
      ∑ d ∈ M.divisors, (μ d : ℂ) *
        ∑ k ∈ Finset.Icc 1 (T / d), g (d * k) := by
  classical
  calc
    _ = ∑ n ∈ Finset.Icc 1 T, (if n.Coprime M then (1 : ℂ) else 0) * g n := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp
    _ = ∑ n ∈ Finset.Icc 1 T,
        (∑ d ∈ M.divisors, if d ∣ n then (μ d : ℂ) else 0) * g n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [coprime_indicator_eq_moebius_sum n M hM]
    _ = ∑ d ∈ M.divisors, (μ d : ℂ) *
        ∑ n ∈ (Finset.Icc 1 T).filter (fun n => d ∣ n), g n := by
      simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_filter, ite_mul, mul_ite,
        zero_mul, mul_zero]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [sum_Icc_dvd_eq_sum_div d T (Nat.pos_of_mem_divisors hd) g]

/-- The actual integer Möbius values have complex norm at most one. -/
theorem moebius_complex_norm_le_one (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

/-- A multiplicative cubic cancellation estimate retains the same power
of the cutoff after imposing coprimality, with one divisor-count factor. -/
theorem coprime_cubic_sum_norm_le (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ T : ℕ,
      ‖∑ n ∈ Finset.Icc 1 T, f n * (n : ℂ) ^ 3‖ ≤ B * (T : ℝ) ^ 3)
    (M T : ℕ) (hM : M ≠ 0) :
    ‖∑ n ∈ (Finset.Icc 1 T).filter (fun n => n.Coprime M), f n * (n : ℂ) ^ 3‖ ≤
      B * (M.divisors.card : ℝ) * (T : ℝ) ^ 3 := by
  classical
  rw [sum_coprime_eq_sum_moebius_multiples _ M T hM]
  have hinner (d : ℕ) :
      (∑ k ∈ Finset.Icc 1 (T / d), f (d * k) * ((d * k : ℕ) : ℂ) ^ 3) =
        f d * (d : ℂ) ^ 3 *
          ∑ k ∈ Finset.Icc 1 (T / d), f k * (k : ℂ) ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, Nat.cast_mul, mul_pow]
    ring
  have hterm (d : ℕ) :
      ‖(μ d : ℂ) * ∑ k ∈ Finset.Icc 1 (T / d),
          f (d * k) * ((d * k : ℕ) : ℂ) ^ 3‖ ≤ B * (T : ℝ) ^ 3 := by
    rw [hinner, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ 1 * (1 * (d : ℝ) ^ 3 * (B * ((T / d : ℕ) : ℝ) ^ 3)) := by
        gcongr
        · exact moebius_complex_norm_le_one d
        · exact hf d
        · exact hbound (T / d)
      _ = B * ((d * (T / d) : ℕ) : ℝ) ^ 3 := by
        push_cast
        ring
      _ ≤ B * (T : ℝ) ^ 3 := by
        gcongr
        exact_mod_cast Nat.mul_div_le T d
  calc
    _ ≤ ∑ d ∈ M.divisors,
        ‖(μ d : ℂ) * ∑ k ∈ Finset.Icc 1 (T / d),
          f (d * k) * ((d * k : ℕ) : ℂ) ^ 3‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ M.divisors, B * (T : ℝ) ^ 3 :=
      Finset.sum_le_sum (fun d _ => hterm d)
    _ = _ := by simp; ring

end QuaternaryQuadraticForms
