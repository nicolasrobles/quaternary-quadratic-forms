import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Inverse-radius weighting of a four-dimensional count

A finite dyadic halving argument turns a bound for the actual sublevel
cardinalities into an inverse-radius weighted sum. The cut is made at
half the largest radius present. Thus its inner set is strictly smaller,
and finite-set induction handles all real radii without logarithmic
rounding or an omitted final shell. Radii below one are excluded explicitly.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- An inverse-radius weighted sum follows from the four-dimensional
sublevel count. The constant is absolute, and the radii may be real. -/
theorem inverseRadiusSum_le_of_sublevel_card
    {α : Type*} (s : Finset α) (r : α → ℝ) (B m U : ℝ)
    (hB : 0 ≤ B) (hm : 0 < m) (hU : 1 ≤ U)
    (hr : ∀ a ∈ s, 1 ≤ r a) (hrU : ∀ a ∈ s, r a ≤ U)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((s.filter (fun a => r a ≤ T)).card : ℝ) ≤ B * (T ^ 4 / m + T ^ 3)) :
    ∑ a ∈ s, 1 / r a ≤ 3 * B * (U ^ 3 / m + U ^ 2) := by
  classical
  induction s using Finset.strongInductionOn generalizing U with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmax⟩ := s.exists_max_image r hs
      let M := r a
      have hM : 1 ≤ M := hr a ha
      have hMpos : 0 < M := zero_lt_one.trans_le hM
      have hMU : M ≤ U := hrU a ha
      let t := s.filter (fun x => r x ≤ M / 2)
      have ht : t ⊆ s := Finset.filter_subset _ _
      have hts : t ⊂ s := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨ht, ?_⟩
        intro heq
        have hat : a ∈ t := heq.symm ▸ ha
        have hhalf := (Finset.mem_filter.mp hat).2
        dsimp [M] at hMpos hhalf
        linarith
      have hcountM : (s.card : ℝ) ≤ B * (M ^ 4 / m + M ^ 3) := by
        have hall : s.filter (fun x => r x ≤ M) = s :=
          Finset.filter_eq_self.mpr hmax
        simpa only [hall] using hcount M hM
      have houter : ∑ x ∈ s \ t, 1 / r x ≤ 2 * B * (M ^ 3 / m + M ^ 2) := by
        have hterm (x : α) (hx : x ∈ s \ t) : 1 / r x ≤ 2 / M := by
          obtain ⟨hxs, hxt⟩ := Finset.mem_sdiff.mp hx
          have hlow : M / 2 < r x := by
            by_contra h
            exact hxt (Finset.mem_filter.mpr ⟨hxs, le_of_not_gt h⟩)
          exact (div_le_div_iff₀ (zero_lt_one.trans_le (hr x hxs)) hMpos).mpr
            (by linarith)
        calc
          _ ≤ ∑ x ∈ s \ t, 2 / M := Finset.sum_le_sum hterm
          _ = ((s \ t).card : ℝ) * (2 / M) := by simp
          _ ≤ (s.card : ℝ) * (2 / M) := mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset)
            (by positivity)
          _ ≤ (B * (M ^ 4 / m + M ^ 3)) * (2 / M) :=
            mul_le_mul_of_nonneg_right hcountM (by positivity)
          _ = _ := by field_simp
      have hinner : ∑ x ∈ t, 1 / r x ≤
          (3 / 4 : ℝ) * B * (M ^ 3 / m + M ^ 2) := by
        by_cases hhalf : 1 ≤ M / 2
        · have htcount (T : ℝ) (hT : 1 ≤ T) :
              ((t.filter (fun x => r x ≤ T)).card : ℝ) ≤
                B * (T ^ 4 / m + T ^ 3) := by
            apply le_trans _ (hcount T hT)
            exact_mod_cast Finset.card_le_card (show
              t.filter (fun x => r x ≤ T) ⊆ s.filter (fun x => r x ≤ T) from by
                intro x hx
                obtain ⟨hxt, hxT⟩ := Finset.mem_filter.mp hx
                exact Finset.mem_filter.mpr ⟨ht hxt, hxT⟩)
          have hi := ih t hts (M / 2) hhalf (fun x hx => hr x (ht hx))
            (fun x hx => (Finset.mem_filter.mp hx).2) htcount
          have hscale : (M / 2) ^ 3 / m + (M / 2) ^ 2 ≤
              (1 / 4 : ℝ) * (M ^ 3 / m + M ^ 2) := by
            have hnon : 0 ≤ M ^ 3 / m := div_nonneg (pow_nonneg hMpos.le _) hm.le
            ring_nf at hnon ⊢
            nlinarith
          calc
            _ ≤ 3 * B * ((M / 2) ^ 3 / m + (M / 2) ^ 2) := hi
            _ ≤ 3 * B * ((1 / 4 : ℝ) * (M ^ 3 / m + M ^ 2)) :=
              mul_le_mul_of_nonneg_left hscale (by positivity)
            _ = _ := by ring
        · have htempty : t = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            have hx' := (Finset.mem_filter.mp hx).2
            have hx1 := hr x (ht hx)
            exact hhalf (hx1.trans hx')
          rw [htempty]
          simp only [Finset.sum_empty]
          positivity
      have hsum := Finset.sum_sdiff_eq_sub (f := fun x => 1 / r x) ht
      have hnon : 0 ≤ B * (M ^ 3 / m + M ^ 2) := by positivity
      have hlocal : ∑ x ∈ s, 1 / r x ≤ 3 * B * (M ^ 3 / m + M ^ 2) := by
        nlinarith [houter, hinner]
      apply hlocal.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 3 * B)
      exact add_le_add
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hMpos.le hMU 3) hm.le)
        (pow_le_pow_left₀ hMpos.le hMU 2)
    · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      rw [hsempty]
      simp only [Finset.sum_empty]
      positivity

end QuaternaryQuadraticForms
