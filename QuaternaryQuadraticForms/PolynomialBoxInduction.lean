import QuaternaryQuadraticForms.PolynomialBoxFiber
import QuaternaryQuadraticForms.PolynomialBoxCombinatorics

/-!
# Polynomial congruences in integer boxes

Induction on the actual number of variables, using the exact one-variable
root count and the weighted expansion of the degenerate-prime product.
The prime polynomials are independent of one another.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Lemma 2.4 over a finite set of distinct primes, with its exact constant. -/
theorem polynomialBox_primeSet_card_le (n E : ℕ) :
    1 ≤ n → 1 ≤ E →
    ∀ (S : Finset ℕ), (∀ p ∈ S, Nat.Prime p) →
    ∀ (P : (p : ℕ) → MvPolynomial (Fin n) (ZMod p)),
      (∀ p ∈ S, P p ≠ 0) → (∀ p ∈ S, (P p).totalDegree ≤ E) →
    ∀ (a b : Fin n → ℤ) (Y : ℝ), 1 ≤ Y →
      (∀ i, ((Finset.Icc (a i) (b i)).card : ℝ) ≤ Y) →
      ((polynomialBoxSolutions S P a b).card : ℝ) ≤
        (polynomialBoxConstant n E : ℝ) ^ S.card *
          (Y ^ n / (∏ p ∈ S, (p : ℝ)) + Y ^ (n - 1)) := by
  classical
  induction n with
  | zero => intro hn; omega
  | succ d ih =>
    intro _hn hE S hS P hP hdeg a b Y hY hI
    have hY0 : 0 ≤ Y := le_trans zero_le_one hY
    by_cases hd : d = 0
    · subst d
      rw [polynomialBoxSolutions_card_succ, integerPolynomialBox_zero,
        Finset.sum_singleton]
      have hb := polynomialIntervalZeros_card_le S hS
        (fun p => polynomialBoxSlice (P p) (fun i => ((Fin.elim0 i : ℤ) : ZMod p)))
        E (fun p hp => polynomialBoxSlice_empty_ne_zero (P p) (hP p hp) _)
        (fun p hp => (polynomialBoxSlice_natDegree_le _ _).trans (hdeg p hp))
        (a 0) (b 0) Y hY0 (hI 0)
      simpa [polynomialIntervalZeros] using hb
    · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
      by_cases hne : S.Nonempty
      · let B := integerPolynomialBox (Fin.tail a) (Fin.tail b)
        let bad : (Fin d → ℤ) → Finset ℕ := polynomialBoxBadPrimes S P
        let Q : (p : ℕ) → MvPolynomial (Fin d) (ZMod p) := fun p =>
          if hp : p ∈ S then
            Classical.choose (exists_polynomialBox_degeneracy_polynomial
              (P p) (hP p hp) E (hdeg p hp))
          else 0
        have hQ (p : ℕ) (hp : p ∈ S) :
            Q p ≠ 0 ∧ (Q p).totalDegree ≤ E ∧
              ∀ y, polynomialBoxSlice (P p) y = 0 → MvPolynomial.eval y (Q p) = 0 := by
          dsimp only [Q]
          rw [dif_pos hp]
          exact Classical.choose_spec (exists_polynomialBox_degeneracy_polynomial
            (P p) (hP p hp) E (hdeg p hp))
        have hdegcount (T : Finset ℕ) (hT : T ⊆ S) :
            ((B.filter fun y => T ⊆ bad y).card : ℝ) ≤
              (polynomialBoxConstant d E : ℝ) ^ T.card *
                (Y ^ d / (∏ p ∈ T, (p : ℝ)) + Y ^ (d - 1)) := by
          have hsub : (B.filter fun y => T ⊆ bad y) ⊆
              polynomialBoxSolutions T Q (Fin.tail a) (Fin.tail b) := by
            intro y hy
            obtain ⟨hy, hTy⟩ := Finset.mem_filter.mp hy
            apply (mem_polynomialBoxSolutions T Q (Fin.tail a) (Fin.tail b) y).mpr
            refine ⟨hy, ?_⟩
            intro p hp
            exact (hQ p (hT hp)).2.2 _ (Finset.mem_filter.mp (hTy hp)).2
          calc
            _ ≤ ((polynomialBoxSolutions T Q (Fin.tail a) (Fin.tail b)).card : ℝ) :=
              by exact_mod_cast Finset.card_le_card hsub
            _ ≤ _ := ih hd1 hE T (fun p hp => hS p (hT hp)) Q
              (fun p hp => (hQ p (hT hp)).1)
              (fun p hp => (hQ p (hT hp)).2.1)
              (Fin.tail a) (Fin.tail b) Y hY (fun i => hI i.succ)
        let f : (Fin d → ℤ) → ℝ := fun y =>
          (polynomialIntervalZeros S
            (fun p => polynomialBoxSlice (P p) (fun i => (y i : ZMod p)))
            (a 0) (b 0)).card
        have hcount := polynomialBox_count_step B S (fun p hp => (hS p hp).two_le)
          hne bad (fun y _ => polynomialBoxBadPrimes_subset S P y)
          (E : ℝ) (polynomialBoxConstant d E : ℝ) Y
          (by exact_mod_cast hE)
          (by exact_mod_cast polynomialBoxConstant_pos d E hd1 hE)
          hY d hd1 f
          (integerPolynomialBox_card_le (Fin.tail a) (Fin.tail b) Y hY0
            (fun i => hI i.succ))
          hdegcount
          (fun y _ => polynomialBox_fiber_card_le S hS P E hE hdeg
            y (a 0) (b 0) Y hY0 (hI 0))
        calc
          ((polynomialBoxSolutions S P a b).card : ℝ) = ∑ y ∈ B, f y := by
            rw [polynomialBoxSolutions_card_succ, Nat.cast_sum]
            rfl
          _ ≤ _ := hcount
          _ = _ := by
            simp only [polynomialBoxConstant_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst S
        rw [polynomialBoxSolutions_empty]
        simp only [Finset.card_empty, pow_zero, Finset.prod_empty, div_one, one_mul]
        exact (integerPolynomialBox_card_le a b Y hY0 hI).trans
          (le_add_of_nonneg_right (pow_nonneg hY0 _))

end QuaternaryQuadraticForms
