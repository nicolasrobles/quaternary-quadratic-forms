import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Lean.Elab.Tactic.Omega

/-!
# Divisibility of the affine quadratic-character sum

The polynomial-sum argument in Lemma 5.9 of the frozen manuscript is applied
to the literal integer-valued quadratic character.  The two polynomials may
have degree at most two; their homogeneity and the geometric good-reduction
conditions are unnecessary for this affine divisibility assertion.

Mathlib's Euler criterion uses the exponent `p / 2`.  For an odd prime this is
the manuscript's `(p - 1) / 2`.  The proof keeps the library's exponent and
verifies the strict degree threshold directly.
-/

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The polynomial `1 - F^(p-1)` is the indicator of the zero locus of `F`
when evaluated over the prime field. -/
theorem quadraticZeroIndicator_eval (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin 4) (ZMod p)) (x : Fin 4 → ZMod p) :
    MvPolynomial.eval x (1 - F ^ (p - 1)) =
      if MvPolynomial.eval x F = 0 then 1 else 0 := by
  classical
  simp only [map_sub, map_one, map_pow, ZMod.pow_card_sub_one]
  by_cases hx : MvPolynomial.eval x F = 0 <;> simp [hx]

/-- The polynomial in the Euler-criterion reduction has zero sum over the
four-dimensional prime-field vector space. -/
theorem quadraticCharacterPolynomial_sum_zero (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (F G : MvPolynomial (Fin 4) (ZMod p))
    (hF : F.totalDegree ≤ 2) (hG : G.totalDegree ≤ 2) :
    (∑ x : Fin 4 → ZMod p,
      MvPolynomial.eval x ((1 - F ^ (p - 1)) * G ^ (p / 2))) = 0 := by
  have hp3 : 3 ≤ p := by
    have hp2 := (Fact.out : p.Prime).two_le
    omega
  have hFpow : (F ^ (p - 1)).totalDegree ≤ (p - 1) * 2 :=
    (MvPolynomial.totalDegree_pow F (p - 1)).trans (Nat.mul_le_mul_left _ hF)
  have hI : (1 - F ^ (p - 1)).totalDegree ≤ (p - 1) * 2 := by
    apply (MvPolynomial.totalDegree_sub 1 (F ^ (p - 1))).trans
    simpa only [MvPolynomial.totalDegree_one, Nat.zero_max] using hFpow
  have hGpow : (G ^ (p / 2)).totalDegree ≤ (p / 2) * 2 :=
    (MvPolynomial.totalDegree_pow G (p / 2)).trans (Nat.mul_le_mul_left _ hG)
  apply MvPolynomial.sum_eval_eq_zero
  calc
    ((1 - F ^ (p - 1)) * G ^ (p / 2)).totalDegree ≤
        (1 - F ^ (p - 1)).totalDegree + (G ^ (p / 2)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ (p - 1) * 2 + (p / 2) * 2 := Nat.add_le_add hI hGpow
    _ < (Fintype.card (ZMod p) - 1) * Fintype.card (Fin 4) := by
      simp only [ZMod.card, Fintype.card_fin]
      omega

/-- The integer-valued quadratic-character sum over the affine zero set of a
quadratic polynomial in four variables is divisible by the odd prime. -/
theorem affineQuadraticCharacterSum_dvd (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (F G : MvPolynomial (Fin 4) (ZMod p))
    (hF : F.totalDegree ≤ 2) (hG : G.totalDegree ≤ 2) :
    (p : ℤ) ∣ ∑ x ∈ Finset.univ.filter (fun x : Fin 4 → ZMod p =>
      MvPolynomial.eval x F = 0), quadraticChar (ZMod p) (MvPolynomial.eval x G) := by
  classical
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [Int.cast_sum, Finset.sum_filter]
  have hχ (m : ZMod p) : (quadraticChar (ZMod p) m : ZMod p) = m ^ (p / 2) := by
    simpa only [ZMod.card] using quadraticChar_eq_pow_of_char_ne_two'
      (by simpa only [ZMod.ringChar_zmod_n] using hp) m
  calc
    (∑ x : Fin 4 → ZMod p, if MvPolynomial.eval x F = 0 then
        (quadraticChar (ZMod p) (MvPolynomial.eval x G) : ZMod p) else 0) =
      ∑ x : Fin 4 → ZMod p,
        MvPolynomial.eval x ((1 - F ^ (p - 1)) * G ^ (p / 2)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [map_mul, quadraticZeroIndicator_eval, map_pow, hχ]
      split_ifs <;> simp
    _ = 0 := quadraticCharacterPolynomial_sum_zero p hp F G hF hG

end QuaternaryQuadraticForms
