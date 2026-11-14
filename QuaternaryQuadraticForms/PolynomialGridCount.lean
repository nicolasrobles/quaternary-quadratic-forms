import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.FieldTheory.Finite.Basic

/-!
# Counting zeros of a ternary quadratic over a prime field

The proved Schwartz--Zippel theorem bounds the actual finite set of zeros.
This form of the estimate is used for the restriction of the quaternary
quadratic form to a three-dimensional hyperplane.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- A nonzero ternary polynomial of degree at most two has at most `2 p²`
zeros in the affine three-space over the prime field. -/
theorem ternary_polynomial_zero_card_le {p : ℕ} [Fact p.Prime]
    (H : MvPolynomial (Fin 3) (ZMod p)) (hH : H ≠ 0)
    (hdeg : H.totalDegree ≤ 2) :
    (Finset.univ.filter (fun y : Fin 3 → ZMod p => MvPolynomial.eval y H = 0)).card ≤
      2 * p ^ 2 := by
  classical
  have h := MvPolynomial.schwartz_zippel_totalDegree hH (Finset.univ : Finset (ZMod p))
  simp only [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] at h
  have hp : (0 : ℚ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hd : (H.totalDegree : ℚ≥0) ≤ 2 := by exact_mod_cast hdeg
  have hb := h.trans (div_le_div_of_nonneg_right hd hp.le)
  have hc := (div_le_div_iff₀ (pow_pos hp 3) hp).mp hb
  have hz :
      ((Finset.univ.filter (fun y : Fin 3 → ZMod p => MvPolynomial.eval y H = 0)).card :
        ℚ≥0) ≤ 2 * (p : ℚ≥0) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hp).mp
    simpa only [pow_succ, mul_assoc] using hc
  exact_mod_cast hz

end QuaternaryQuadraticForms
