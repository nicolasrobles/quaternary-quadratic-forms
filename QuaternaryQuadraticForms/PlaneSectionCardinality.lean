import QuaternaryQuadraticForms.FourierRays
import QuaternaryQuadraticForms.PlaneRestriction
import QuaternaryQuadraticForms.PolynomialGridCount
import QuaternaryQuadraticForms.ConicParametrization
import Mathlib.Tactic.Linarith

/-!
# The cardinality of every nonzero plane section

The affine cone over the actual projective plane section decomposes into
the zero vector and `p - 1` vectors on each projective ray. The nonzero
ternary quadratic restriction has at most `2 p²` affine zeros, giving at
most `2 p + 2` projective section points. These statements also apply to
tangent planes and singular plane sections.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

local instance planeSectionCardinality_projectiveFintype (p : ℕ) [Fact p.Prime] :
    Fintype (PrimeProjective p) := Fintype.ofFinite _

/-- The affine zeros of the actual quadratic form and plane equation consist
of zero and the `p - 1` nonzero vectors on each projective section point. -/
theorem planeSection_affine_card_eq {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (u : Fin 4 → ZMod p) :
    (Finset.univ.filter (fun x : PrimeVector p =>
      quadraticValue A x = 0 ∧ dotProduct u x = 0)).card =
      1 + (p - 1) *
        ((projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0)).card := by
  classical
  let C : PrimeVector p → Prop := fun x => quadraticValue A x = 0 ∧ dotProduct u x = 0
  have h0 : C 0 := by simp [C, quadraticValue]
  have hC (a : (ZMod p)ˣ) (x : PrimeVector p) : C (a • x) ↔ C x := by
    exact and_congr (quadraticValue_units_zero_iff A a x)
      (dotProduct_units_smul_zero_iff u x a)
  calc
    (Finset.univ.filter C).card = ∑ x : PrimeVector p, if C x then 1 else 0 :=
      Finset.card_filter C Finset.univ
    _ = 1 + ∑ x : {x : PrimeVector p // x ≠ 0}, if C x.val then 1 else 0 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun x => if C x then (1 : ℕ) else 0) 0]
      rw [if_pos h0]
    _ = 1 + ∑ P : PrimeProjective p, ∑ a : (ZMod p)ˣ,
        if C (a • P.rep) then 1 else 0 := by
      rw [sum_nonzero_eq_sum_projective (K := ZMod p)
        (fun x : PrimeVector p => if C x then (1 : ℕ) else 0)]
    _ = 1 + (p - 1) *
        ((projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0)).card := by
      simp_rw [hC]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card_units]
      rw [← Finset.mul_sum, ← Finset.card_filter]
      simp [projectiveQuadric, Finset.filter_filter, C]

/-- The actual affine zero set of a nonsingular quadratic form on a nonzero
plane has at most `2 p²` points, even when the section is singular. -/
theorem planeSection_affine_card_le (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (u : Fin 4 → ZMod p) (hu : u ≠ 0) :
    (Finset.univ.filter (fun x : PrimeVector p =>
      quadraticValue A x = 0 ∧ dotProduct u x = 0)).card ≤ 2 * p ^ 2 := by
  classical
  obtain ⟨e, H, hH, hdeg, heval⟩ :=
    exists_plane_quadratic_restriction A hA hdet (primeField_two_ne_zero p hp) u hu
  let eZeros : {y : Fin 3 → ZMod p // MvPolynomial.eval y H = 0} ≃
      {x : PrimeVector p // quadraticValue A x = 0 ∧ dotProduct u x = 0} :=
    { toFun := fun y =>
        ⟨(e y.val).val, (heval y.val).symm.trans y.property, (e y.val).property⟩
      invFun := fun x => ⟨e.symm ⟨x.val, x.property.2⟩, by
        rw [heval, e.apply_symm_apply]
        exact x.property.1⟩
      left_inv := fun y => by
        apply Subtype.ext
        change e.symm (e y.val) = y.val
        exact e.symm_apply_apply y.val
      right_inv := fun x => by
        apply Subtype.ext
        change (e (e.symm ⟨x.val, x.property.2⟩)).val = x.val
        exact congrArg (fun z : planeSubspace u => z.val)
          (e.apply_symm_apply ⟨x.val, x.property.2⟩) }
  have hcard := Fintype.card_congr eZeros
  simp only [Fintype.card_subtype] at hcard
  rw [← hcard]
  exact ternary_polynomial_zero_card_le H hH hdeg

/-- Every nonzero plane cuts the nonsingular quaternary quadric in at most
`2 p + 2` rational projective points. No condition on the dual form is used. -/
theorem planeSection_card_le (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (u : Fin 4 → ZMod p) (hu : u ≠ 0) :
    ((projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0)).card ≤ 2 * p + 2 := by
  classical
  have hbound := planeSection_affine_card_le p hp A hA hdet u hu
  rw [planeSection_affine_card_eq] at hbound
  have hp2 := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hprod : (p - 1) * p + p = p ^ 2 := by
    calc
      (p - 1) * p + p = (p - 1 + 1) * p := by ring
      _ = p ^ 2 := by rw [hpred]; ring
  by_contra h
  have hcard : 2 * p + 3 ≤
      ((projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0)).card := by omega
  have hmul := Nat.mul_le_mul_left (p - 1) hcard
  nlinarith

/-- The elementary exceptional-plane bound for the literal projective
character sum, using the actual section cardinality and character norms. -/
theorem projectiveSectionTrace_norm_le (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.transpose = A)
    (hdet : A.det ≠ 0) (u : Fin 4 → ZMod p) (hu : u ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (G : MvPolynomial (Fin 4) (ZMod p)) :
    ‖projectiveSectionTrace A ψ G u‖ ≤ 2 * (p : ℝ) + 2 := by
  classical
  unfold projectiveSectionTrace
  calc
    ‖∑ P ∈ (projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0),
        polynomialCharacterWeight ψ G P.rep‖ ≤
      ∑ P ∈ (projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0),
        ‖polynomialCharacterWeight ψ G P.rep‖ := norm_sum_le _ _
    _ ≤ ∑ _P ∈ (projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0),
        (1 : ℝ) :=
      Finset.sum_le_sum (fun P _ => polynomialCharacterWeight_norm_le_one ψ G P.rep)
    _ = (((projectiveQuadric A).filter (fun P => dotProduct u P.rep = 0)).card : ℝ) := by simp
    _ ≤ 2 * (p : ℝ) + 2 := by exact_mod_cast planeSection_card_le p hp A hA hdet u hu

end QuaternaryQuadraticForms
