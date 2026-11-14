import QuaternaryQuadraticForms.GoodReduction
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Ring

/-!
# Rank failure for two rows

The rank condition in the definition of good reduction is equivalent to
the simultaneous vanishing of the literal two-by-two minors. We retain
all ordered pairs of columns; the repeated and zero minors do not alter
their common zero set.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Two rows fail to have rank two exactly when every two-by-two minor
vanishes. The assertion also covers a zero row and an empty column set. -/
theorem rank_two_ne_iff_minors_zero {N : ℕ} {K : Type*} [Field K]
    (a b : Fin N → K) :
    Matrix.rank ![a, b] ≠ 2 ↔
      ∀ i j, a i * b j - a j * b i = 0 := by
  classical
  change (¬ Matrix.rank ![a, b] = 2) ↔ _
  rw [rank_two_iff_linearIndependent, linearIndependent_fin2]
  change (¬ (b ≠ 0 ∧ ∀ c : K, c • b ≠ a)) ↔ _
  constructor
  · intro h i j
    by_cases hb : b = 0
    · subst b
      simp
    · obtain ⟨c, hc⟩ : ∃ c : K, c • b = a := by
        by_contra hn
        exact h ⟨hb, fun c hc => hn ⟨c, hc⟩⟩
      rw [← hc]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro h
    rintro ⟨hb, hs⟩
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hb (funext hn)
    apply hs (a i / b i)
    funext j
    change a i / b i * b j = a j
    calc
      a i / b i * b j = (a i * b j) / b i := by ring
      _ = a j := (div_eq_iff hi).mpr (sub_eq_zero.mp (h i j))

/-- Full rank is witnessed by one nonzero two-by-two minor. -/
theorem rank_two_iff_exists_minor_ne_zero {N : ℕ} {K : Type*} [Field K]
    (a b : Fin N → K) :
    Matrix.rank ![a, b] = 2 ↔
      ∃ i j, a i * b j - a j * b i ≠ 0 := by
  classical
  have h := not_congr (rank_two_ne_iff_minors_zero a b)
  simpa only [not_not, not_forall] using h

end QuaternaryQuadraticForms
