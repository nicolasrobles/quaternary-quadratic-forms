import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A divisor and harmonic bound for the actual gcd sum

For each positive divisor, division by that divisor injects its
positive multiples below a cutoff into the same positive interval.
The gcd itself occurs among the common divisors. Summing these
finite inequalities gives the uniform bound needed for Lemma 3.6.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Positive multiples of a fixed divisor contribute at most the
ordinary harmonic sum after division by that divisor. -/
theorem sum_divisor_multiples_div_le_harmonic (d T : ℕ) (hd : d ≠ 0) :
    (∑ n ∈ Finset.Icc 1 T, if d ∣ n then (d : ℝ) / (n : ℝ) else 0) ≤
      (harmonic T : ℝ) := by
  classical
  let s := (Finset.Icc 1 T).filter (fun n => d ∣ n)
  have hmap (n : ℕ) (hn : n ∈ s) : 1 ≤ n / d ∧ n / d ≤ T := by
    have hmem := Finset.mem_filter.mp hn
    have hinterval := Finset.mem_Icc.mp hmem.1
    refine ⟨Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hinterval.1)
      hmem.2) (Nat.pos_of_ne_zero hd), ?_⟩
    exact (Nat.div_le_self n d).trans hinterval.2
  have hinj : Set.InjOn (fun n : ℕ => n / d) s := by
    intro n hn m hm hnm
    have hn' := (Finset.mem_filter.mp hn).2
    have hm' := (Finset.mem_filter.mp hm).2
    calc
      n = n / d * d := (Nat.div_mul_cancel hn').symm
      _ = m / d * d := congrArg (fun j => j * d) hnm
      _ = m := Nat.div_mul_cancel hm'
  have hterm (n : ℕ) (hn : n ∈ s) :
      (d : ℝ) / (n : ℝ) = 1 / ((n / d : ℕ) : ℝ) := by
    have hmem := Finset.mem_filter.mp hn
    have hnpos := (Finset.mem_Icc.mp hmem.1).1
    have hjpos := (hmap n hn).1
    have hnzero : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnpos)
    have hjzero : ((n / d : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hjpos)
    apply (div_eq_div_iff hnzero hjzero).mpr
    have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' hmem.2
    simpa only [one_mul] using hmul
  calc
    _ = ∑ n ∈ s, (d : ℝ) / (n : ℝ) := by
      simp only [s, Finset.sum_filter]
    _ = ∑ n ∈ s, 1 / ((n / d : ℕ) : ℝ) :=
      Finset.sum_congr rfl hterm
    _ = ∑ j ∈ s.image (fun n => n / d), 1 / (j : ℝ) :=
      (Finset.sum_image (f := fun j : ℕ => (1 : ℝ) / (j : ℝ)) hinj).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 T, 1 / (j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_Icc.mpr (hmap n hn)
      · intro j _ _
        positivity
    _ = (harmonic T : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]

private theorem gcd_div_le_sum_divisors (n M : ℕ) (hM : M ≠ 0) :
    (n.gcd M : ℝ) / (n : ℝ) ≤
      ∑ d ∈ M.divisors, if d ∣ n then (d : ℝ) / (n : ℝ) else 0 := by
  have hmem : n.gcd M ∈ M.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n M, hM⟩
  have h := Finset.single_le_sum
    (f := fun d : ℕ => if d ∣ n then (d : ℝ) / (n : ℝ) else 0)
    (fun d _ => by dsimp only; split_ifs <;> positivity) hmem
  simpa only [if_pos (Nat.gcd_dvd_left n M)] using h

/-- The finite gcd sum is bounded by the actual divisor count times
the ordinary harmonic sum, uniformly in both natural parameters. -/
theorem sum_gcd_div_le_divisor_card_mul_harmonic (T M : ℕ) (hM : M ≠ 0) :
    (∑ n ∈ Finset.Icc 1 T, (n.gcd M : ℝ) / (n : ℝ)) ≤
      (M.divisors.card : ℝ) * (harmonic T : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 T,
        ∑ d ∈ M.divisors, if d ∣ n then (d : ℝ) / (n : ℝ) else 0 :=
      Finset.sum_le_sum (fun n _ => gcd_div_le_sum_divisors n M hM)
    _ = ∑ d ∈ M.divisors,
        ∑ n ∈ Finset.Icc 1 T, if d ∣ n then (d : ℝ) / (n : ℝ) else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _d ∈ M.divisors, (harmonic T : ℝ) :=
      Finset.sum_le_sum (fun d hd =>
        sum_divisor_multiples_div_le_harmonic d T (Nat.pos_of_mem_divisors hd).ne')
    _ = _ := by simp

/-- The real-cutoff gcd estimate has one divisor factor and a logarithm,
including the boundary cutoff `X=1`. -/
theorem sum_gcd_div_le_divisor_card_mul_log (M : ℕ) (hM : M ≠ 0)
    (X : ℝ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n.gcd M : ℝ) / (n : ℝ)) ≤
      (M.divisors.card : ℝ) * (1 + Real.log X) := by
  exact (sum_gcd_div_le_divisor_card_mul_harmonic ⌊X⌋₊ M hM).trans
    (mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log X hX) (Nat.cast_nonneg _))

end QuaternaryQuadraticForms
