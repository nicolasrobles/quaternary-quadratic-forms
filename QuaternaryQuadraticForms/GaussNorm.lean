import QuaternaryQuadraticForms.QuadraticGaussSums
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.BigOperators

/-!
# Squared norms of the actual Gauss sums at arbitrary positive moduli

Translation expresses the product with the conjugate as a bilinear character
sum. Composite-modulus orthogonality selects the actual kernel of twice the
matrix. The argument includes modulus one and imposes no good-prime condition.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem stdAddChar_residue_sum {ι : Type*} (n : ℕ) [NeZero n]
    (s : Finset ι) (f : ι → ZMod n) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, ih]

/-- Four-coordinate additive orthogonality at every positive modulus,
including composite moduli and modulus one. -/
theorem stdAddChar_residue_vector_orthogonality (n : ℕ) [NeZero n]
    (c : Fin 4 → ZMod n) :
    (∑ z : Fin 4 → ZMod n, ZMod.stdAddChar (dotProduct c z)) =
      if c = 0 then (n : ℂ) ^ 4 else 0 := by
  classical
  have hscalar (d : ZMod n) :
      (∑ z : ZMod n, ZMod.stdAddChar (d * z)) =
        if d = 0 then (n : ℂ) else 0 := by
    simpa only [mul_comm d, ZMod.card, apply_ite, Nat.cast_zero] using
      AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar n)
  have hsum :
      (∑ z : Fin 4 → ZMod n, ZMod.stdAddChar (dotProduct c z)) =
        ∏ i : Fin 4, (if c i = 0 then (n : ℂ) else 0) := by
    simp_rw [dotProduct, stdAddChar_residue_sum]
    rw [← Fintype.prod_sum (fun (i : Fin 4) (z : ZMod n) => ZMod.stdAddChar (c i * z))]
    simp_rw [hscalar]
  rw [hsum]
  by_cases hc : c = 0
  · subst c
    simp
  · rw [if_neg hc]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    change c i ≠ 0 at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem stdAddChar_residue_conj (n : ℕ) [NeZero n] (t : ZMod n) :
    (starRingEnd ℂ) (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _)).symm

private theorem matrix_residue_bilinear_orthogonality (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (a : (ZMod n)ˣ)
    (z : Fin 4 → ZMod n) :
    (∑ x : Fin 4 → ZMod n,
      ZMod.stdAddChar (2 * (a : ZMod n) * dotProduct x (A.mulVec z))) =
      if (2 : ZMod n) • A.mulVec z = 0 then (n : ℂ) ^ 4 else 0 := by
  have hphase (x : Fin 4 → ZMod n) :
      2 * (a : ZMod n) * dotProduct x (A.mulVec z) =
        dotProduct ((2 * (a : ZMod n)) • A.mulVec z) x := by
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm]
  simp_rw [hphase]
  rw [stdAddChar_residue_vector_orthogonality]
  have hzero : (2 * (a : ZMod n)) • A.mulVec z = 0 ↔
      (2 : ZMod n) • A.mulVec z = 0 := by
    rw [mul_comm (2 : ZMod n) (a : ZMod n)]
    simp only [funext_iff, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      mul_assoc, Units.mul_right_eq_zero]
  simp only [hzero]

/-- The product of the literal Gauss sum with its conjugate is the
character sum on the actual kernel of twice the matrix. -/
theorem quadraticGaussSum_mul_conj_eq_kernel_sum (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (hA : A.transpose = A)
    (a : (ZMod n)ˣ) (u : Fin 4 → ZMod n) :
    quadraticGaussSum n A (a : ZMod n) u *
        (starRingEnd ℂ) (quadraticGaussSum n A (a : ZMod n) u) =
      (n : ℂ) ^ 4 *
        ∑ z ∈ Finset.univ.filter (fun z : Fin 4 → ZMod n =>
          (2 : ZMod n) • A.mulVec z = 0),
          ZMod.stdAddChar ((a : ZMod n) * dotProduct z (A.mulVec z) + dotProduct u z) := by
  classical
  let f : (Fin 4 → ZMod n) → ℂ := fun x =>
    ZMod.stdAddChar ((a : ZMod n) * dotProduct x (A.mulVec x) + dotProduct u x)
  have htranslated (x z : Fin 4 → ZMod n) :
      f (x + z) * (starRingEnd ℂ) (f x) =
        f z * ZMod.stdAddChar (2 * (a : ZMod n) * dotProduct x (A.mulVec z)) := by
    dsimp only [f]
    rw [stdAddChar_residue_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    have hcross : dotProduct z (A.mulVec x) = dotProduct x (A.mulVec z) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
    rw [hcross]
    ring
  change (∑ x, f x) * (starRingEnd ℂ) (∑ x, f x) = _
  calc
    _ = ∑ x : Fin 4 → ZMod n, ∑ y : Fin 4 → ZMod n,
        f y * (starRingEnd ℂ) (f x) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ x : Fin 4 → ZMod n, ∑ z : Fin 4 → ZMod n,
        f (x + z) * (starRingEnd ℂ) (f x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Equiv.sum_comp (Equiv.addLeft x)
        (fun y => f y * (starRingEnd ℂ) (f x))).symm
    _ = ∑ z : Fin 4 → ZMod n, ∑ x : Fin 4 → ZMod n,
        f (x + z) * (starRingEnd ℂ) (f x) := Finset.sum_comm
    _ = ∑ z : Fin 4 → ZMod n,
        f z * ∑ x : Fin 4 → ZMod n,
          ZMod.stdAddChar (2 * (a : ZMod n) * dotProduct x (A.mulVec z)) := by
      simp_rw [htranslated, ← Finset.mul_sum]
    _ = ∑ z : Fin 4 → ZMod n,
        f z * (if (2 : ZMod n) • A.mulVec z = 0 then (n : ℂ) ^ 4 else 0) := by
      simp_rw [matrix_residue_bilinear_orthogonality]
    _ = _ := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> simp [f, mul_comm]

/-- The squared norm is bounded by the modulus to the fourth power times
the cardinality of the actual kernel of twice the matrix. No nonsingularity
or oddness assumption is needed, and modulus one is included. -/
theorem quadraticGaussSum_norm_sq_le_kernel_card (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (hA : A.transpose = A)
    (a : (ZMod n)ˣ) (u : Fin 4 → ZMod n) :
    ‖quadraticGaussSum n A (a : ZMod n) u‖ ^ 2 ≤
      (n : ℝ) ^ 4 *
        ((Finset.univ.filter (fun z : Fin 4 → ZMod n =>
          (2 : ZMod n) • A.mulVec z = 0)).card : ℝ) := by
  classical
  have hnorm := congrArg (fun w : ℂ => ‖w‖)
    (quadraticGaussSum_mul_conj_eq_kernel_sum n A hA a u)
  simp only [norm_mul, Complex.norm_conj, ← pow_two, norm_pow,
    Complex.norm_natCast] at hnorm
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg n) 4)
  calc
    _ ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin 4 → ZMod n =>
        (2 : ZMod n) • A.mulVec z = 0),
        ‖ZMod.stdAddChar ((a : ZMod n) * dotProduct z (A.mulVec z) + dotProduct u z)‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [ZMod.stdAddChar_apply, Circle.norm_coe,
      Finset.sum_const, nsmul_eq_mul, mul_one]

end QuaternaryQuadraticForms
