import QuaternaryQuadraticForms.EuclideanIntegerBox
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# Clearing denominators in a rational quaternary normal form

A single positive integer clears the inverse change of variables and the binary
coefficients.  The resulting integral linear map is injective and sends each
integral zero of the original form to an integral zero of the split model.
Its coordinate growth is bounded by a constant depending only on that map.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A finite family of rational numbers has a common positive integer denominator. -/
theorem rational_family_clear_denominators {ι : Type*} [Finite ι] (f : ι → ℚ) :
    ∃ k : ℤ, 0 < k ∧ ∃ w : ι → ℤ, ∀ i, (w i : ℚ) = (k : ℚ) * f i := by
  obtain ⟨k, hk⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) f
  have h : ∀ i, ∃ z : ℤ, (z : ℚ) = ((k : ℤ) : ℚ) * f i := by
    intro i
    obtain ⟨z, hz⟩ := hk i
    exact ⟨z, by simpa only [Algebra.smul_def, eq_intCast] using hz⟩
  choose w hw using h
  exact ⟨k, k.property, w, hw⟩

/-- A fixed integral matrix has uniformly bounded coordinate growth in the
actual Euclidean norm of the integer lattice. -/
theorem integerMatrix_coordinate_bound (L : Matrix (Fin 4) (Fin 4) ℤ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ z : Fin 4 → ℤ, ∀ i : Fin 4,
      |((L.mulVec z) i : ℝ)| ≤ D * integerEuclideanNorm z := by
  let total : ℝ := ∑ i, ∑ j, |(L i j : ℝ)|
  have htotal : 0 ≤ total := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨1 + total, by linarith, ?_⟩
  intro z i
  have hrow : (∑ j, |(L i j : ℝ)|) ≤ total := by
    exact Finset.single_le_sum (f := fun i : Fin 4 => ∑ j, |(L i j : ℝ)|)
      (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  calc
    |((L.mulVec z) i : ℝ)| = |∑ j, (L i j : ℝ) * (z j : ℝ)| := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
    _ ≤ ∑ j, |(L i j : ℝ) * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |(L i j : ℝ)| * |(z j : ℝ)| := by simp only [abs_mul]
    _ ≤ ∑ j, |(L i j : ℝ)| * integerEuclideanNorm z := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (coordinate_abs_le_integerEuclideanNorm z j)
          (abs_nonneg _)
    _ = (∑ j, |(L i j : ℝ)|) * integerEuclideanNorm z := by rw [Finset.sum_mul]
    _ ≤ (1 + total) * integerEuclideanNorm z := by
      exact mul_le_mul_of_nonneg_right (by linarith) (integerEuclideanNorm_nonneg z)

/-- Clear the denominators of an exact rational normal form, preserving
injectivity of the change of lattice variables and binary anisotropy. -/
theorem rationalQuadric_integer_model
    (S T : Matrix (Fin 4) (Fin 4) ℚ) (hT : T.det ≠ 0)
    (a b c : ℚ)
    (hnormal : ∀ y : Fin 4 → ℚ,
      dotProduct (T.mulVec y) (S.mulVec (T.mulVec y)) =
        y 0 * y 1 + a * y 2 ^ 2 + b * y 2 * y 3 + c * y 3 ^ 2)
    (haniso : ∀ x y : ℚ, a * x ^ 2 + b * x * y + c * y ^ 2 = 0 →
      x = 0 ∧ y = 0) :
    ∃ (k a' b' c' : ℤ) (L : Matrix (Fin 4) (Fin 4) ℤ),
      k ≠ 0 ∧ Function.Injective L.mulVec ∧
      (∀ x y : ℤ, a' * x ^ 2 + b' * x * y + c' * y ^ 2 = 0 →
        x = 0 ∧ y = 0) ∧
      ∀ z : Fin 4 → ℤ,
        dotProduct (fun i => (z i : ℚ)) (S.mulVec (fun i => (z i : ℚ))) = 0 →
        k * (L.mulVec z) 0 * (L.mulVec z) 1 + a' * (L.mulVec z) 2 ^ 2 +
          b' * (L.mulVec z) 2 * (L.mulVec z) 3 + c' * (L.mulVec z) 3 ^ 2 = 0 := by
  let f : ((Fin 4 × Fin 4) ⊕ Fin 3) → ℚ :=
    Sum.elim (fun ij => T⁻¹ ij.1 ij.2) ![a, b, c]
  obtain ⟨k, hk, w, hw⟩ := rational_family_clear_denominators f
  let L : Matrix (Fin 4) (Fin 4) ℤ := fun i j => w (.inl (i, j))
  let a' : ℤ := w (.inr 0)
  let b' : ℤ := w (.inr 1)
  let c' : ℤ := w (.inr 2)
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hL (i j : Fin 4) : (L i j : ℚ) = (k : ℚ) * T⁻¹ i j := by
    exact hw (.inl (i, j))
  have ha : (a' : ℚ) = (k : ℚ) * a := hw (.inr 0)
  have hb : (b' : ℚ) = (k : ℚ) * b := hw (.inr 1)
  have hc : (c' : ℚ) = (k : ℚ) * c := hw (.inr 2)
  have hcast (z : Fin 4 → ℤ) :
      (fun i => ((L.mulVec z) i : ℚ)) =
        (k : ℚ) • T⁻¹.mulVec (fun i => (z i : ℚ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, hL, Finset.mul_sum, mul_assoc]
  have hTL (z : Fin 4 → ℤ) :
      T.mulVec (fun i => ((L.mulVec z) i : ℚ)) =
        (k : ℚ) • (fun i => (z i : ℚ)) := by
    rw [hcast, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT), Matrix.one_mulVec]
  refine ⟨k, a', b', c', L, ne_of_gt hk, ?_, ?_, ?_⟩
  · intro x y hxy
    have h := congrArg (fun v : Fin 4 → ℤ =>
      T.mulVec (fun i => (v i : ℚ))) hxy
    dsimp only at h
    rw [hTL, hTL] at h
    funext i
    have hi : (k : ℚ) * (x i : ℚ) = (k : ℚ) * (y i : ℚ) := congrFun h i
    exact_mod_cast (mul_left_cancel₀ hkQ hi)
  · intro x y hxy
    have hQ : (a' : ℚ) * (x : ℚ) ^ 2 + (b' : ℚ) * (x : ℚ) * (y : ℚ) +
        (c' : ℚ) * (y : ℚ) ^ 2 = 0 := by exact_mod_cast hxy
    rw [ha, hb, hc] at hQ
    have hz : (k : ℚ) * (a * (x : ℚ) ^ 2 + b * (x : ℚ) * (y : ℚ) +
        c * (y : ℚ) ^ 2) = 0 := by linear_combination hQ
    obtain ⟨hx, hy⟩ := haniso x y ((mul_eq_zero.mp hz).resolve_left hkQ)
    exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩
  · intro z hz
    have hzero : dotProduct (T.mulVec (fun i => ((L.mulVec z) i : ℚ)))
        (S.mulVec (T.mulVec (fun i => ((L.mulVec z) i : ℚ)))) = 0 := by
      rw [hTL, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hz]
      simp
    rw [hnormal] at hzero
    have hmodel : (k : ℚ) * ((L.mulVec z) 0 : ℚ) * ((L.mulVec z) 1 : ℚ) +
        (a' : ℚ) * ((L.mulVec z) 2 : ℚ) ^ 2 +
        (b' : ℚ) * ((L.mulVec z) 2 : ℚ) * ((L.mulVec z) 3 : ℚ) +
        (c' : ℚ) * ((L.mulVec z) 3 : ℚ) ^ 2 = 0 := by
      rw [ha, hb, hc]
      linear_combination (k : ℚ) * hzero
    exact_mod_cast hmodel

end QuaternaryQuadraticForms
