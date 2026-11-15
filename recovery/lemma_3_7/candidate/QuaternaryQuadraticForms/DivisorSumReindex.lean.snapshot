import QuaternaryQuadraticForms.CoprimeCubicBound
import QuaternaryQuadraticForms.ModulusNormSum

/-!
# Exact finite divisor rearrangements

Positive divisors below a finite cutoff are reindexed by their positive
quotients. The gcd restriction and coprimality conditions are retained
literally, including cutoffs smaller than a factor and the empty interval.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The finite divisor hyperbola rearrangement, with positive indices
and the exact natural quotient cutoff. -/
theorem sum_Icc_divisors_eq_sum_mul (T : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 T, ∑ h ∈ n.divisors, F n h) =
      ∑ h ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 (T / h), F (h * k) h := by
  classical
  have hdivisors (n : ℕ) (hn : n ∈ Finset.Icc 1 T) :
      n.divisors = (Finset.Icc 1 T).filter (fun h => h ∣ n) := by
    have hmem := Finset.mem_Icc.mp hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hmem.1
    ext h
    constructor
    · intro hh
      have hdvd := Nat.dvd_of_mem_divisors hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hh, (Nat.le_of_dvd hnpos hdvd).trans hmem.2⟩, hdvd⟩
    · intro hh
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hh).2, hnpos.ne'⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 T, if h ∣ n then F n h else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hdivisors n hn, Finset.sum_filter]
    _ = ∑ h ∈ Finset.Icc 1 T, ∑ n ∈ Finset.Icc 1 T, if h ∣ n then F n h else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.sum_filter]
      exact sum_Icc_dvd_eq_sum_div h T (Finset.mem_Icc.mp hh).1 (fun n => F n h)

/-- A literal gcd-restricted interval is exactly the multiples of the
shared factor whose quotient is coprime to the complementary factor. -/
theorem sum_gcdModuliUpTo_eq_sum_coprime (q d e T : ℕ) (hd : 0 < d)
    (hqde : q = d * e) (F : ℕ → ℂ) :
    (∑ c ∈ gcdModuliUpTo q d T, F c) =
      ∑ n ∈ (Finset.Icc 1 (T / d)).filter (fun n => n.Coprime e), F (d * n) := by
  classical
  have hcancel (n : ℕ) : (d * n).gcd q = d ↔ n.Coprime e := by
    rw [hqde, Nat.gcd_mul_left]
    constructor
    · intro h
      exact Nat.eq_of_mul_eq_mul_left hd (by simpa only [mul_one] using h)
    · intro h
      rw [h.gcd_eq_one, mul_one]
  simp only [gcdModuliUpTo, Finset.sum_filter]
  calc
    _ = ∑ c ∈ Finset.Icc 1 T,
        if d ∣ c then (if c.gcd q = d then F c else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hdc : d ∣ c
      · simp only [if_pos hdc]
      · have hgc : c.gcd q ≠ d := by
          intro heq
          exact hdc (heq ▸ Nat.gcd_dvd_left c q)
        simp only [if_neg hdc, if_neg hgc]
    _ = ∑ n ∈ Finset.Icc 1 (T / d),
        if (d * n).gcd q = d then F (d * n) else 0 := by
      rw [← Finset.sum_filter]
      exact sum_Icc_dvd_eq_sum_div d T hd (fun c => if c.gcd q = d then F c else 0)
    _ = _ := by simp only [hcancel]

/-- The finite divisor rearrangement keeps both coprimality restrictions:
the divisor is coprime to both fixed factors and the quotient to the second. -/
theorem sum_coprime_divisors_eq_sum_mul (T d e : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => n.Coprime e),
      ∑ h ∈ n.divisors.filter (fun h => h.Coprime d), F h (n / h)) =
      ∑ h ∈ (Finset.Icc 1 T).filter (fun h => h.Coprime (d * e)),
        ∑ k ∈ (Finset.Icc 1 (T / h)).filter (fun k => k.Coprime e), F h k := by
  classical
  calc
    _ = ∑ n ∈ Finset.Icc 1 T, ∑ h ∈ n.divisors,
        if n.Coprime e ∧ h.Coprime d then F h (n / h) else 0 := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only
      by_cases hn : n.Coprime e
      · rw [if_pos hn]
        apply Finset.sum_congr rfl
        intro h _
        by_cases hhd : h.Coprime d
        · rw [if_pos hhd, if_pos ⟨hn, hhd⟩]
        · rw [if_neg hhd, if_neg (fun h => hhd h.2)]
      · rw [if_neg hn]
        symm
        apply Finset.sum_eq_zero
        intro h _
        exact if_neg (fun h => hn h.1)
    _ = ∑ h ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 (T / h),
        if (h * k).Coprime e ∧ h.Coprime d then F h ((h * k) / h) else 0 :=
      sum_Icc_divisors_eq_sum_mul T
        (fun n h => if n.Coprime e ∧ h.Coprime d then F h (n / h) else 0)
    _ = _ := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only
      have hpos : 0 < h := (Finset.mem_Icc.mp hh).1
      simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
      by_cases hhcop : h.Coprime d ∧ h.Coprime e
      · rw [if_pos hhcop]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.mul_div_cancel_left k hpos]
        by_cases hk : k.Coprime e
        · rw [if_pos ⟨⟨hhcop.2, hk⟩, hhcop.1⟩, if_pos hk]
        · rw [if_neg (fun h => hk h.1.2), if_neg hk]
      · rw [if_neg hhcop]
        apply Finset.sum_eq_zero
        intro k _
        exact if_neg (fun h => hhcop ⟨h.2, h.1.1⟩)

end QuaternaryQuadraticForms
