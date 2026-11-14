import QuaternaryQuadraticForms.QuadraticCharacter
import QuaternaryQuadraticForms.WeilBound
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Quadratic character sums of arbitrary cubics

The cubic in the diagonal pencil need not be separable.  Over a perfect field,
a nonseparable cubic has a repeated linear factor over the base field itself.
Its quadratic character sum is exactly the negative of one character value;
this includes the triple-root case.  Together with the registered affine Weil
estimate for separable cubics, this proves the bound needed in Lemma 4.6.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Polynomial
open scoped BigOperators

private theorem linear_eq_C_mul_X_sub_C {K : Type*} [Field K]
    (f : K[X]) (hf : f.natDegree = 1) :
    ∃ c a : K, c ≠ 0 ∧ f = C c * (X - C a) := by
  obtain ⟨c, hc, d, hcd⟩ := Polynomial.natDegree_eq_one.mp hf
  refine ⟨c, -d / c, hc, ?_⟩
  rw [← hcd, mul_sub, ← C_mul]
  have h : c * (-d / c) = -d := by field_simp
  rw [h, C_neg, sub_neg_eq_add]

/-- A repeated root of a cubic over a perfect field descends to that field.
The two roots in this factorization are allowed to coincide. -/
theorem nonseparable_cubic_factorization {K : Type*} [Field K] [PerfectField K]
    (f : K[X]) (hf : f.natDegree = 3) (hsep : ¬f.Separable) :
    ∃ c a b : K, c ≠ 0 ∧ f = C c * (X - C a) ^ 2 * (X - C b) := by
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hsq : ¬Squarefree f := fun h =>
    hsep (PerfectField.separable_iff_squarefree.mpr h)
  rw [squarefree_iff_no_irreducibles hf0] at hsq
  push_neg at hsq
  obtain ⟨g, hg, hgf⟩ := hsq
  have hgg0 : g * g ≠ 0 := mul_ne_zero hg.ne_zero hg.ne_zero
  have hdeg : g.natDegree + g.natDegree ≤ 3 := by
    simpa only [natDegree_mul hg.ne_zero hg.ne_zero, hf] using
      natDegree_le_of_dvd hgf hf0
  have hg1 : g.natDegree = 1 := by
    have := hg.natDegree_pos
    omega
  obtain ⟨q, hq⟩ := hgf
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
    exact hf0 hq
  have hq1 : q.natDegree = 1 := by
    have h := congrArg Polynomial.natDegree hq
    rw [hf, natDegree_mul hgg0 hq0, natDegree_mul hg.ne_zero hg.ne_zero, hg1] at h
    omega
  obtain ⟨c, a, hc, hga⟩ := linear_eq_C_mul_X_sub_C g hg1
  obtain ⟨d, b, hd, hqb⟩ := linear_eq_C_mul_X_sub_C q hq1
  refine ⟨c ^ 2 * d, a, b, mul_ne_zero (pow_ne_zero 2 hc) hd, ?_⟩
  rw [hq, hga, hqb, C_mul, C_pow]
  ring

/-- The exact repeated-root cubic sum.  If the two roots coincide, both
sides vanish; otherwise the sum consists of one omitted character value. -/
theorem quadraticChar_repeated_cubic_sum (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (c a b : ZMod p) :
    (∑ x : ZMod p, complexQuadraticChar p (c * (x - a) ^ 2 * (x - b))) =
      -complexQuadraticChar p (c * (a - b)) := by
  classical
  have hshift : (∑ x : ZMod p, complexQuadraticChar p (x - b)) = 0 := by
    calc
      _ = ∑ x : ZMod p, complexQuadraticChar p x :=
        (Equiv.subRight b).sum_comp _
      _ = 0 := MulChar.sum_eq_zero_of_ne_one (complexQuadraticChar_ne_one p hp)
  have hlinear : (∑ x : ZMod p, complexQuadraticChar p (c * (x - b))) = 0 := by
    simp only [map_mul, ← Finset.mul_sum, hshift, mul_zero]
  have hvalue (x : ZMod p) (hx : x ≠ a) :
      complexQuadraticChar p (c * (x - a) ^ 2 * (x - b)) =
        complexQuadraticChar p (c * (x - b)) := by
    have hsq : complexQuadraticChar p ((x - a) ^ 2) = 1 := by
      rw [complexQuadraticChar_apply, quadraticChar_sq_one' (sub_ne_zero.mpr hx)]
      norm_num
    rw [map_mul, map_mul, hsq, mul_one, map_mul]
  have hsum :
      (∑ x ∈ Finset.univ.erase a,
        complexQuadraticChar p (c * (x - a) ^ 2 * (x - b))) =
      ∑ x ∈ Finset.univ.erase a, complexQuadraticChar p (c * (x - b)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hvalue x (Finset.ne_of_mem_erase hx)
  have hfull := Finset.sum_erase_add Finset.univ
    (fun x : ZMod p => complexQuadraticChar p (c * (x - a) ^ 2 * (x - b)))
    (Finset.mem_univ a)
  have hlin := Finset.sum_erase_add Finset.univ
    (fun x : ZMod p => complexQuadraticChar p (c * (x - b)))
    (Finset.mem_univ a)
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
    MulChar.map_zero, add_zero] at hfull
  rw [hsum] at hfull
  rw [hlinear] at hlin
  exact hfull.symm.trans (eq_neg_of_add_eq_zero_left hlin)

/-- A nonseparable cubic has quadratic character sum of norm at most one. -/
theorem quadraticChar_nonseparable_cubic_sum_norm_le_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (f : Polynomial (ZMod p)) (hf : f.natDegree = 3) (hsep : ¬f.Separable) :
    ‖∑ x : ZMod p, complexQuadraticChar p (f.eval x)‖ ≤ 1 := by
  obtain ⟨c, a, b, _, hfactor⟩ := nonseparable_cubic_factorization f hf hsep
  simp only [hfactor, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  rw [quadraticChar_repeated_cubic_sum p hp, norm_neg]
  exact DirichletCharacter.norm_le_one (complexQuadraticChar p) _

/-- The quadratic character sum of every cubic, including repeated-root
cubics, satisfies the same degree-three Weil bound. -/
theorem quadraticChar_cubic_sum_norm_le
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (f : Polynomial (ZMod p)) (hf : f.natDegree = 3) :
    ‖∑ x : ZMod p, complexQuadraticChar p (f.eval x)‖ ≤ 2 * Real.sqrt p := by
  have hp2 : p ≠ 2 := by omega
  by_cases hsep : f.Separable
  · have h := weil_bound_of_separable p (complexQuadraticChar p)
      (complexQuadraticChar_ne_one p hp2) f (by omega) hsep
    simpa only [hf, Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] using h
  · apply (quadraticChar_nonseparable_cubic_sum_norm_le_one p hp2 f hf hsep).trans
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    have hs : (1 : ℝ) ≤ Real.sqrt p := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp1
    linarith

/-- Removing a finite set costs at most its cardinality, with no
separability condition on the cubic. -/
theorem quadraticChar_cubic_sum_sdiff_norm_le
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (f : Polynomial (ZMod p)) (hf : f.natDegree = 3) (T : Finset (ZMod p)) :
    ‖∑ x ∈ Finset.univ \ T, complexQuadraticChar p (f.eval x)‖ ≤
      2 * Real.sqrt p + T.card := by
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ T)]
  calc
    _ ≤ ‖∑ x : ZMod p, complexQuadraticChar p (f.eval x)‖ +
          ‖∑ x ∈ T, complexQuadraticChar p (f.eval x)‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt p + T.card := by
      apply add_le_add (quadraticChar_cubic_sum_norm_le p hp f hf)
      calc
        _ ≤ ∑ x ∈ T, ‖complexQuadraticChar p (f.eval x)‖ := norm_sum_le _ _
        _ ≤ ∑ _x ∈ T, (1 : ℝ) := Finset.sum_le_sum fun x _ =>
          DirichletCharacter.norm_le_one (complexQuadraticChar p) (f.eval x)
        _ = T.card := by simp

/-- The four excluded pencil parameters contribute at most four to the
unscaled cubic character sum. -/
theorem quadraticChar_cubic_sum_sdiff_four_norm_le
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (f : Polynomial (ZMod p)) (hf : f.natDegree = 3)
    (T : Finset (ZMod p)) (hT : T.card ≤ 4) :
    ‖∑ x ∈ Finset.univ \ T, complexQuadraticChar p (f.eval x)‖ ≤
      2 * Real.sqrt p + 4 := by
  apply (quadraticChar_cubic_sum_sdiff_norm_le p hp f hf T).trans
  exact add_le_add_left (by exact_mod_cast hT) _

end QuaternaryQuadraticForms
