import QuaternaryQuadraticForms.QuadricCounting
import QuaternaryQuadraticForms.GeneralPrimeGauss
import QuaternaryQuadraticForms.GoodPrime

/-!
# Exact affine and projective quadric point counts

The general-matrix prime Gauss formula is summed over every scalar, with
the zero scalar retained. Orthogonality and the actual projective-ray
partition give the source count, with its integer-valued Legendre symbol.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The exact affine zero count for a nonsingular symmetric quaternary
form over an odd prime field, including the origin. -/
theorem affineQuadric_card_complex (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ((affineQuadricPoints A).card : ℂ) =
      (p : ℂ) ^ 3 + complexQuadraticChar p A.det * ((p : ℂ) ^ 2 - p) := by
  classical
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hnz : Fintype.card {a : ZMod p // a ≠ 0} = p - 1 := by
    rw [← Fintype.card_congr (unitsEquivNeZero : (ZMod p)ˣ ≃ {a : ZMod p // a ≠ 0})]
    exact ZMod.card_units p
  have hs : (∑ a : {a : ZMod p // a ≠ 0}, quadraticGaussSum p A a.val 0) =
      ((p : ℂ) - 1) * (complexQuadraticChar p A.det * (p : ℂ) ^ 2) := by
    calc
      _ = ∑ _ : {a : ZMod p // a ≠ 0},
          complexQuadraticChar p A.det * (p : ℂ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        exact quadraticGaussSum_prime_zero_frequency p hp A hA hdet a.val a.property
      _ = _ := by simp [hnz, Nat.cast_sub hp1]
  have hsum : (∑ a : ZMod p, quadraticGaussSum p A a 0) =
      (p : ℂ) ^ 4 + ((p : ℂ) - 1) *
        (complexQuadraticChar p A.det * (p : ℂ) ^ 2) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => quadraticGaussSum p A a 0) 0,
      quadraticGaussSum_zero, hs]
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hpC
  rw [affineQuadric_card_additive, hsum]
  ring

/-- The affine point count as an equality of integers with the actual
integer-valued quadratic character. -/
theorem affineQuadric_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ((affineQuadricPoints A).card : ℤ) =
      (p : ℤ) ^ 3 + quadraticChar (ZMod p) A.det * ((p : ℤ) ^ 2 - p) := by
  have h := affineQuadric_card_complex p hp A hA hdet
  simp only [complexQuadraticChar_apply] at h
  exact_mod_cast h

/-- The actual projective quadric has exactly the source cardinality. -/
theorem projectiveQuadric_card_complex (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ((projectiveQuadric A).card : ℂ) =
      (p : ℂ) ^ 2 + (1 + complexQuadraticChar p A.det) * p + 1 := by
  have h := affineQuadric_card_complex p hp A hA hdet
  rw [affineQuadric_card_projective] at h
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (Fact.out : p.Prime).ne_one
  apply mul_left_cancel₀ hp1
  calc
    ((p : ℂ) - 1) * (projectiveQuadric A).card =
        ((p : ℂ) ^ 3 + complexQuadraticChar p A.det * ((p : ℂ) ^ 2 - p)) - 1 := by
      rw [← h]
      ring
    _ = ((p : ℂ) - 1) *
        ((p : ℂ) ^ 2 + (1 + complexQuadraticChar p A.det) * p + 1) := by ring

/-- The exact projective cardinality with its integer-valued quadratic character. -/
theorem projectiveQuadric_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ((projectiveQuadric A).card : ℤ) =
      (p : ℤ) ^ 2 + (1 + quadraticChar (ZMod p) A.det) * p + 1 := by
  have h := projectiveQuadric_card_complex p hp A hA hdet
  simp only [complexQuadraticChar_apply] at h
  exact_mod_cast h

/-- Lemma 3.2(iii) for the source integral matrix at every prime outside
the exact modulus `N_F = 2 |det A|`. -/
theorem integral_projectiveQuadric_card (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A) :
    ((projectiveQuadric (reduceQuadraticMatrix p A)).card : ℤ) =
      (p : ℤ) ^ 2 + (1 + legendreSym p A.det) * p + 1 := by
  have h := projectiveQuadric_card p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp)
  have hdet : (A.det : ZMod p) = (reduceQuadraticMatrix p A).det :=
    (Int.castRingHom (ZMod p)).map_det A
  rw [← hdet] at h
  exact h

end QuaternaryQuadraticForms
