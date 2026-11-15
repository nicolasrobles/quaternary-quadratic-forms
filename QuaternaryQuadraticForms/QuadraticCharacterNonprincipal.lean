import QuaternaryQuadraticForms.QuadraticCharacterPeriod
import QuaternaryQuadraticForms.QuadraticJacobiWitness
import Mathlib.Data.Nat.Squarefree

/-!
# Nonprincipality from the actual nonsquare integer

The character at level `4 * |α|` is nonprincipal when `α` is nonzero
and nonsquare. The proof uses squarefree decomposition, quadratic
reciprocity, and actual unit lifting between finite residue rings.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem jacobi_reciprocity_one_mod_eight (a n : ℕ) (ha : a ≠ 0)
    (hn : n % 8 = 1) : jacobiSym (a : ℤ) n = jacobiSym (n : ℤ) a := by
  have hn2 : n % 2 = 1 := by omega
  have hn4 : n % 4 = 1 := by omega
  have hno : Odd n := Nat.odd_iff.mpr hn2
  have h2n : jacobiSym 2 n = 1 := by
    rw [jacobiSym.at_two hno, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [hn2, hn]
  have hn2j : jacobiSym (n : ℤ) 2 = 1 := by
    rw [jacobiSym.mod_left, ← Int.natCast_mod, hn2]
    simp
  obtain ⟨e, a', ha', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha 2 (by decide)
  have hao : Odd a' := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ha')
  haveI : NeZero a' := ⟨hao.pos.ne'⟩
  rw [he, Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.pow_left,
    Nat.cast_ofNat, h2n, one_pow, one_mul, jacobiSym.mul_right,
    jacobiSym.pow_right, hn2j, one_pow, one_mul]
  exact jacobiSym.quadratic_reciprocity_one_mod_four' hao hn4

private theorem squarefree_has_odd_prime (s : ℕ) (hs : Squarefree s)
    (hs1 : s ≠ 1) (hs2 : s ≠ 2) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ s := by
  obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd hs1
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨t, ht⟩ := hps
    have ht1 : t ≠ 1 := by
      intro h
      apply hs2
      simpa [h] using ht
    obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht1
    refine ⟨p, hp, ?_, dvd_trans hpt (by rw [ht]; exact dvd_mul_left t 2)⟩
    intro hp2
    subst p
    have hsq : 2 * 2 ∣ s := by rw [ht]; exact Nat.mul_dvd_mul_left 2 hpt
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hsq
  · exact ⟨p, hp, hp2, hps⟩

private theorem lift_jacobi_witness (α δ : ℤ) (b : ℕ) (hα : α ≠ 0) (hδ : δ ≠ 0)
    (hfac : α = (b : ℤ) ^ 2 * δ) (n : ℕ)
    (hn : n.Coprime (2 * δ.natAbs)) (hjn : jacobiSym δ n = -1) :
    ∃ N : ℕ, N.Coprime (2 * α.natAbs) ∧ jacobiSym α N = -1 := by
  have habs : α.natAbs = b ^ 2 * δ.natAbs := by
    rw [hfac, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  have hdiv : 4 * δ.natAbs ∣ 4 * α.natAbs := by
    rw [habs]
    exact ⟨b ^ 2, by ring⟩
  haveI : NeZero (4 * α.natAbs) := ⟨mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hα)⟩
  haveI : NeZero (4 * δ.natAbs) := ⟨mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hδ)⟩
  let u : (ZMod (4 * δ.natAbs))ˣ :=
    ZMod.unitOfCoprime n ((goodQuadraticChar_coprime_four_iff δ n).mpr hn)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdiv u
  let N : ℕ := (v : ZMod (4 * α.natAbs)).val
  have hN4 : N.Coprime (4 * α.natAbs) := ZMod.val_coe_unit_coprime v
  have hNg : N.Coprime (2 * α.natAbs) :=
    (goodQuadraticChar_coprime_four_iff α N).mp hN4
  have hNδ4 : N.Coprime (4 * δ.natAbs) := Nat.Coprime.of_dvd_right hdiv hN4
  have hNδ : N.Coprime (2 * δ.natAbs) :=
    (goodQuadraticChar_coprime_four_iff δ N).mp hNδ4
  have hcast : (N : ZMod (4 * δ.natAbs)) = (n : ZMod (4 * δ.natAbs)) := by
    have hval := congrArg (fun w : (ZMod (4 * δ.natAbs))ˣ =>
      (w : ZMod (4 * δ.natAbs))) hv
    change (ZMod.cast (v : ZMod (4 * α.natAbs)) : ZMod (4 * δ.natAbs)) =
      (ZMod.unitOfCoprime n ((goodQuadraticChar_coprime_four_iff δ n).mpr hn) :
        ZMod (4 * δ.natAbs)) at hval
    rw [ZMod.coe_unitOfCoprime] at hval
    rw [← ZMod.natCast_zmod_val (v : ZMod (4 * α.natAbs)), ZMod.cast_natCast hdiv] at hval
    exact hval
  have hcoeff := congrArg (goodQuadraticDirichletChar δ hδ) hcast
  simp only [goodQuadraticDirichletChar_natCast,
    goodQuadraticChar_of_coprime _ _ hn, goodQuadraticChar_of_coprime _ _ hNδ,
    globalQuadraticChar] at hcoeff
  have hjN : jacobiSym δ N = -1 := by
    exact (Int.cast_injective hcoeff).trans hjn
  have hbdvd : b ∣ α.natAbs := by
    rw [habs]
    exact ⟨b * δ.natAbs, by ring⟩
  have hNb : N.Coprime b :=
    Nat.Coprime.of_dvd_right hbdvd (Nat.coprime_mul_iff_right.mp hNg).2
  have hsq : jacobiSym ((b : ℤ) ^ 2) N = 1 :=
    jacobiSym.sq_one' (by simpa only [Int.gcd_natCast_natCast] using hNb.symm)
  refine ⟨N, hNg, ?_⟩
  rw [hfac, jacobiSym.mul_left, hsq, one_mul, hjN]

private theorem squarefree_signed_jacobi_witness (s : ℕ) (hs : Squarefree s)
    (hs1 : s ≠ 1) : ∃ n : ℕ, n.Coprime (2 * s) ∧
      jacobiSym (s : ℤ) n = -1 ∧ jacobiSym (-(s : ℤ)) n = -1 := by
  by_cases hs2 : s = 2
  · subst s
    refine ⟨5, by decide, ?_, ?_⟩
    · norm_num only [Nat.cast_ofNat]
      rw [jacobiSym.at_two (by decide : Odd 5)]
      rfl
    · norm_num only [Nat.cast_ofNat]
      rw [jacobiSym.at_neg_two (by decide : Odd 5)]
      rfl
  obtain ⟨p, hp, hp2, hps⟩ := squarefree_has_odd_prime s hs hs1 hs2
  obtain ⟨n, hn8, hncp, hjn⟩ :=
    exists_jacobiSym_neg_one_mod_eight_of_squarefree s p hs hp hp2 hps
  have hn2 : n % 2 = 1 := by omega
  have hn4 : n % 4 = 1 := by omega
  have hno : Odd n := Nat.odd_iff.mpr hn2
  have hjs : jacobiSym (s : ℤ) n = -1 :=
    (jacobi_reciprocity_one_mod_eight s n hs.ne_zero hn8).trans hjn
  refine ⟨n, Nat.coprime_mul_iff_right.mpr ⟨Nat.coprime_two_right.mpr hno, hncp⟩,
    hjs, ?_⟩
  rw [jacobiSym.neg _ hno, ZMod.χ₄_nat_one_mod_four hn4, one_mul, hjs]

/-- Every nonzero nonsquare integer has an actual negative Jacobi value at
a positive modulus coprime to `2 * |α|`. Square factors are removed and
the witness is lifted back to a unit at the full modulus. -/
theorem exists_good_jacobiSym_neg_one (α : ℤ) (hα : α ≠ 0)
    (hns : ¬IsSquare α) :
    ∃ n : ℕ, n.Coprime (2 * α.natAbs) ∧ jacobiSym α n = -1 := by
  obtain ⟨s, b, hspos, _, hbs, hs⟩ :=
    Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hα)
  have hsz : (s : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hspos.ne'
  by_cases hs1 : s = 1
  · subst s
    rcases Int.natAbs_eq α with ha | ha
    · exfalso
      apply hns
      refine ⟨(b : ℤ), ?_⟩
      rw [ha, ← hbs]
      push_cast
      ring
    · refine lift_jacobi_witness α (-1) b hα (by decide) ?_ 3 (by decide) ?_
      · rw [ha, ← hbs]
        push_cast
        ring
      · rw [jacobiSym.at_neg_one (by decide : Odd 3)]
        rfl
  obtain ⟨n, hnc, hjpos, hjneg⟩ := squarefree_signed_jacobi_witness s hs hs1
  rcases Int.natAbs_eq α with ha | ha
  · refine lift_jacobi_witness α (s : ℤ) b hα hsz ?_ n ?_ hjpos
    · rw [ha, ← hbs]
      push_cast
      rfl
    · simpa only [Int.natAbs_natCast] using hnc
  · refine lift_jacobi_witness α (-(s : ℤ)) b hα (neg_ne_zero.mpr hsz) ?_ n ?_ hjneg
    · rw [ha, ← hbs]
      push_cast
      ring
    · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hnc

/-- Nonsquareness of the original integer proves nonprincipality of the
actual good-modulus Dirichlet character; this is not an extra premise. -/
theorem goodQuadraticDirichletChar_ne_one (α : ℤ) (hα : α ≠ 0)
    (hns : ¬IsSquare α) : goodQuadraticDirichletChar α hα ≠ 1 := by
  obtain ⟨n, hn, hjn⟩ := exists_good_jacobiSym_neg_one α hα hns
  intro h
  have hnunit : IsUnit (n : ZMod (4 * α.natAbs)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr ((goodQuadraticChar_coprime_four_iff α n).mpr hn)
  have he := congrArg (fun χ : DirichletCharacter ℂ (4 * α.natAbs) =>
    χ (n : ZMod (4 * α.natAbs))) h
  simp only [goodQuadraticDirichletChar_natCast,
    goodQuadraticChar_of_coprime _ _ hn, globalQuadraticChar,
    hjn, Int.cast_neg, Int.cast_one, MulChar.one_apply hnunit] at he
  norm_num at he

/-- The complete period of the actual good Jacobi coefficient cancels,
with nonsquareness derived from the original integer parameter. -/
theorem goodQuadraticChar_sum_period_eq_zero (α : ℤ) (hα : α ≠ 0)
    (hns : ¬IsSquare α) :
    ∑ n ∈ Finset.range (4 * α.natAbs), goodQuadraticChar α n = 0 := by
  let P := 4 * α.natAbs
  have hP : 0 < P := Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hα)
  letI : NeZero P := ⟨hP.ne'⟩
  let χ : DirichletCharacter ℂ P := goodQuadraticDirichletChar α hα
  have hcast (Q : ℕ) [NeZero Q] (n : Fin Q) :
      ((n : ℕ) : ZMod Q) = (ZMod.finEquiv Q) n := by
    cases Q with
    | zero => exact Fin.elim0 n
    | succ Q => exact Fin.cast_val_eq_self n
  have hs : ∑ n ∈ Finset.range P, χ (n : ZMod P) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [hcast]
    exact ((ZMod.finEquiv P).toEquiv.sum_comp χ).trans
      (MulChar.sum_eq_zero_of_ne_one (goodQuadraticDirichletChar_ne_one α hα hns))
  simpa only [χ, P, goodQuadraticDirichletChar_natCast] using hs

end QuaternaryQuadraticForms
