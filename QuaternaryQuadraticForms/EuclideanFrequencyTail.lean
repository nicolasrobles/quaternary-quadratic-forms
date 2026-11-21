import QuaternaryQuadraticForms.EuclideanIntegerBox
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Absolute lattice tails in four Euclidean dimensions -/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem radius_card_bound (s : Finset (Fin 4 → ℤ)) (R : ℝ) (hR : 1 ≤ R)
    (hs : ∀ u ∈ s, integerEuclideanNorm u ≤ R) : (s.card : ℝ) ≤ (3*R)^4 := by
  let box := integerPolynomialBox (fun _ : Fin 4 => -⌊R⌋) (fun _ => ⌊R⌋)
  have hsub : s ⊆ box := fun u hu => integerEuclideanNorm_le_mem_box R u (hs u hu)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (integerPolynomialBox_card_le _ _ _ (by positivity) (fun _ =>
      integerEuclideanInterval_card_le_three_mul R hR))

private theorem finite_frequency_tail (s : Finset (Fin 4 → ℤ)) (k : ℕ) (hk : 1 ≤ k)
    (U : ℝ) (hU : 1 ≤ U) (hs : ∀ u ∈ s, U < integerEuclideanNorm u) :
    ∑ u ∈ s, 1 / integerEuclideanNorm u ^ (k+4) ≤ 2592 / U^k := by
  classical
  induction s using Finset.strongInductionOn generalizing U with
  | _ s ih =>
    by_cases hn : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image integerEuclideanNorm hn
      let M := integerEuclideanNorm a
      have hUM : U < M := hs a ha
      have hM : 1 ≤ M := hU.trans hUM.le
      have hMpos : 0 < M := zero_lt_one.trans_le hM
      let far := s.filter (fun u => 2*M < integerEuclideanNorm u)
      have hfar : far ⊆ s := Finset.filter_subset _ _
      have hproper : far ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr ⟨hfar, ?_⟩
        intro heq
        have hmem : a ∈ far := heq.symm ▸ ha
        have : 2*M < M := (Finset.mem_filter.mp hmem).2
        linarith
      have hm2 : 1 ≤ 2*M := by linarith
      have habove := ih far hproper (2*M) hm2 (fun _ hu => (Finset.mem_filter.mp hu).2)
      have hnear : ((s \ far).card : ℝ) ≤ (3*(2*M))^4 := by
        apply radius_card_bound _ _ hm2
        intro u hu
        obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
        exact le_of_not_gt (fun hr => huf (Finset.mem_filter.mpr ⟨hus, hr⟩))
      have hbelow : ∑ u ∈ s \ far, 1 / integerEuclideanNorm u^(k+4) ≤ 1296 / M^k := by
        calc
          _ ≤ ∑ _u ∈ s \ far, 1 / M^(k+4) := by
            apply Finset.sum_le_sum
            intro u hu
            exact one_div_le_one_div_of_le (pow_pos hMpos _) (pow_le_pow_left₀ hMpos.le
              (hmin u (Finset.mem_sdiff.mp hu).1) _)
          _ = ((s \ far).card : ℝ) * (1 / M^(k+4)) := by simp
          _ ≤ (3*(2*M))^4 * (1 / M^(k+4)) :=
            mul_le_mul_of_nonneg_right hnear (by positivity)
          _ = 1296 / M^k := by rw [pow_add]; field_simp; ring
      have htwo : (2 : ℝ) ≤ 2^k := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
      have hhalf : 2592 / (2*M)^k ≤ 1296 / M^k := by
        rw [mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right htwo (pow_nonneg hMpos.le k)]
      have hsplit := Finset.sum_sdiff_eq_sub (f := fun u => 1 / integerEuclideanNorm u^(k+4)) hfar
      calc
        _ ≤ 2592 / M^k := by
          rw [← sub_add_cancel (∑ u ∈ s, _) (∑ u ∈ far, _), ← hsplit]
          exact (add_le_add hbelow (habove.trans hhalf)).trans_eq (by ring)
        _ ≤ 2592 / U^k := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact pow_le_pow_left₀ (by positivity) hUM.le k
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty]
      positivity

/-- For every exponent j=k+4 with k≥1, the absolute tail is at most 2592 U⁻ᵏ. -/
theorem integerEuclidean_frequency_tail (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 1 ≤ U) :
    let f := fun u : Fin 4 → ℤ => if U < integerEuclideanNorm u then
      1 / integerEuclideanNorm u^(k+4) else 0
    Summable f ∧ ∑' u, f u ≤ 2592 / U^k := by
  classical
  intro f
  have hn : 0 ≤ f := by
    intro u
    dsimp [f]
    split_ifs
    · exact div_nonneg zero_le_one (pow_nonneg (integerEuclideanNorm_nonneg _) _)
    · rfl
  have hbound (s : Finset (Fin 4 → ℤ)) : ∑ u ∈ s, f u ≤ 2592 / U^k := by
    dsimp [f]
    rw [← Finset.sum_filter]
    exact finite_frequency_tail _ k hk U hU (fun _ hu => (Finset.mem_filter.mp hu).2)
  have hsum := summable_of_sum_le hn hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end QuaternaryQuadraticForms
