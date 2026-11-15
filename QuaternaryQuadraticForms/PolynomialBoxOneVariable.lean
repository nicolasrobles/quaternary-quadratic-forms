import QuaternaryQuadraticForms.PolynomialBoxResidues
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

/-!
# Polynomial congruences in one integer variable

Each prime has its own polynomial.  Nonvanishing is required only at the
primes whose congruences are imposed.  The count includes the empty prime
set, so it also applies to the completely degenerate fibers in the
dimension induction for Lemma 2.4.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual integer solutions of the prime polynomial congruences in
the interval. -/
def polynomialIntervalZeros (S : Finset ℕ)
    (P : (p : ℕ) → Polynomial (ZMod p)) (a b : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc a b).filter
    (fun z => ∀ p ∈ S, (P p).eval (z : ZMod p) = 0)

/-- Membership records exactly the interval and the polynomial
congruences, with no coefficient or common-polynomial restriction. -/
theorem mem_polynomialIntervalZeros (S : Finset ℕ)
    (P : (p : ℕ) → Polynomial (ZMod p)) (a b z : ℤ) :
    z ∈ polynomialIntervalZeros S P a b ↔
      a ≤ z ∧ z ≤ b ∧ ∀ p ∈ S, (P p).eval (z : ZMod p) = 0 := by
  classical
  simp only [polynomialIntervalZeros, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The exact one-variable interval bound used in the source proof of
Lemma 2.4. -/
theorem polynomialIntervalZeros_card_le
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (P : (p : ℕ) → Polynomial (ZMod p)) (E : ℕ)
    (hP : ∀ p ∈ S, P p ≠ 0) (hdeg : ∀ p ∈ S, (P p).natDegree ≤ E)
    (a b : ℤ) (Y : ℝ) (hY : 0 ≤ Y)
    (hI : ((Finset.Icc a b).card : ℝ) ≤ Y) :
    ((polynomialIntervalZeros S P a b).card : ℝ) ≤
      (E : ℝ) ^ S.card * (Y / (∏ p ∈ S, (p : ℝ)) + 1) := by
  classical
  let R (p : S) : Finset (ZMod p.val) := by
    letI : Fact p.val.Prime := ⟨hS p.val p.property⟩
    exact (P p.val).roots.toFinset
  have hR (p : S) : (R p).card ≤ E := by
    letI : Fact p.val.Prime := ⟨hS p.val p.property⟩
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (hdeg p.val p.property))
  have hcount : polynomialIntervalZeros S P a b = primeResidueInterval S R a b := by
    ext z
    rw [mem_polynomialIntervalZeros, mem_primeResidueInterval]
    apply and_congr_right
    intro _ha
    apply and_congr_right
    intro _hb
    constructor
    · intro hz p
      letI : Fact p.val.Prime := ⟨hS p.val p.property⟩
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (hP p.val p.property)).mpr (hz p.val p.property))
    · intro hz p hp
      letI : Fact p.Prime := ⟨hS p hp⟩
      exact (Polynomial.mem_roots (hP p hp)).mp
        (Multiset.mem_toFinset.mp (hz ⟨p, hp⟩))
  rw [hcount]
  exact primeResidueInterval_card_le S hS R E hR a b Y hY hI

end QuaternaryQuadraticForms
