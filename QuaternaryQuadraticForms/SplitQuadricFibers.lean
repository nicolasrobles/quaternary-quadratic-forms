import QuaternaryQuadraticForms.DivisorPowerBound
import QuaternaryQuadraticForms.EuclideanIntegerBox
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Divisor bounds for the nonzero fibres of a split quaternary form

Negative divisors are retained explicitly. A fixed first coordinate determines
the second coordinate when the binary value is nonzero.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The integral binary part of the split form. -/
def splitQuadricBinaryValue (a b c x y : ℤ) : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2

/-- Both signs of the positive divisors of an integer. -/
def splitQuadricSignedDivisors (n : ℤ) : Finset ℤ :=
  n.natAbs.divisors.image (fun d : ℕ => (d : ℤ)) ∪
    n.natAbs.divisors.image (fun d : ℕ => -(d : ℤ))

/-- A divisor of a nonzero integer belongs to the finite set of signed divisors. -/
theorem splitQuadric_mem_signedDivisors {n z : ℤ} (hn : n ≠ 0) (hz : z ∣ n) :
    z ∈ splitQuadricSignedDivisors n := by
  have hd : z.natAbs ∈ n.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hz, Int.natAbs_ne_zero.mpr hn⟩
  by_cases hpos : 0 ≤ z
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨z.natAbs, hd, by simp [abs_of_nonneg hpos]⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨z.natAbs, hd, by simp [abs_of_neg (lt_of_not_ge hpos)]⟩

/-- Counting both signs costs at most a factor two. -/
theorem splitQuadric_signedDivisors_card_le (n : ℤ) :
    (splitQuadricSignedDivisors n).card ≤ 2 * n.natAbs.divisors.card := by
  calc
    _ ≤ (n.natAbs.divisors.image (fun d : ℕ => (d : ℤ))).card +
        (n.natAbs.divisors.image (fun d : ℕ => -(d : ℤ))).card := Finset.card_union_le _ _
    _ ≤ n.natAbs.divisors.card + n.natAbs.divisors.card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = _ := by omega

/-- A nonzero binary fibre has at most twice the positive-divisor count. -/
theorem splitQuadric_nonzero_fiber_card_le (k a b c : ℤ) (hk : k ≠ 0)
    (s : Finset (Fin 4 → ℤ)) (x y : ℤ)
    (hn : splitQuadricBinaryValue a b c x y ≠ 0)
    (htail : ∀ z ∈ s, z 2 = x ∧ z 3 = y)
    (heq : ∀ z ∈ s,
      k * z 0 * z 1 + a * z 2 ^ 2 + b * z 2 * z 3 + c * z 3 ^ 2 = 0) :
    s.card ≤ 2 * (splitQuadricBinaryValue a b c x y).natAbs.divisors.card := by
  classical
  have hprod (z : Fin 4 → ℤ) (hz : z ∈ s) :
      k * z 0 * z 1 = -splitQuadricBinaryValue a b c x y := by
    have h := heq z hz
    obtain ⟨h2, h3⟩ := htail z hz
    rw [h2, h3] at h
    dsimp [splitQuadricBinaryValue]
    linarith
  have hfirst (z : Fin 4 → ℤ) (hz : z ∈ s) : z 0 ≠ 0 := by
    intro hzero
    have h := hprod z hz
    rw [hzero, mul_zero, zero_mul] at h
    exact hn (neg_eq_zero.mp h.symm)
  calc
    s.card ≤ (splitQuadricSignedDivisors (splitQuadricBinaryValue a b c x y)).card := by
      apply Finset.card_le_card_of_injOn (fun z : Fin 4 → ℤ => z 0)
      · intro z hz
        apply splitQuadric_mem_signedDivisors hn
        refine ⟨-(k * z 1), ?_⟩
        have h := hprod z hz
        nlinarith
      · intro z hz w hw h0
        change z 0 = w 0 at h0
        have h1 : z 1 = w 1 := by
          apply mul_left_cancel₀ (mul_ne_zero hk (hfirst z hz))
          rw [hprod z hz, h0, hprod w hw]
        have h2 : z 2 = w 2 := (htail z hz).1.trans (htail w hw).1.symm
        have h3 : z 3 = w 3 := (htail z hz).2.trans (htail w hw).2.symm
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
    _ ≤ _ := splitQuadric_signedDivisors_card_le _

end QuaternaryQuadraticForms
