import QuaternaryQuadraticForms.IntegralGaussSums
import QuaternaryQuadraticForms.FourierOrthogonality

/-!
# Affine and projective counts of the actual quadratic zero set

Additive orthogonality expresses the affine count through the literal Gauss
sums. The proved projective-ray bijection removes the origin and accounts
for every nonzero scalar on each projective point.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators LinearAlgebra.Projectivization

local instance quadricCountProjectiveFintype (p : ℕ) [Fact p.Prime] :
    Fintype (PrimeProjective p) := Fintype.ofFinite _

/-- The actual affine quadratic zero set, including the origin. -/
def affineQuadricPoints {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) : Finset (PrimeVector p) := by
  classical
  exact Finset.univ.filter (fun x => quadraticValue A x = 0)

/-- The affine count is the additive-character average of the actual Gauss sums. -/
theorem affineQuadric_card_additive (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) :
    (p : ℂ) * (affineQuadricPoints A).card =
      ∑ a : ZMod p, quadraticGaussSum p A a 0 := by
  classical
  simp only [quadraticGaussSum, zero_dotProduct, add_zero]
  rw [Finset.sum_comm]
  simp_rw [stdAddChar_orthogonality]
  change (p : ℂ) * (affineQuadricPoints A).card =
    ∑ x : PrimeVector p, if quadraticValue A x = 0 then (p : ℂ) else 0
  rw [← Finset.sum_filter]
  simp [affineQuadricPoints, mul_comm]

/-- The origin contributes one and every projective zero contributes exactly
`p-1` nonzero affine vectors. -/
theorem affineQuadric_card_projective (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) :
    ((affineQuadricPoints A).card : ℂ) =
      1 + ((p : ℂ) - 1) * (projectiveQuadric A).card := by
  classical
  let f : PrimeVector p → ℂ := fun x => if quadraticValue A x = 0 then 1 else 0
  have haff : ((affineQuadricPoints A).card : ℂ) = ∑ x, f x := by
    simp [affineQuadricPoints, f]
  have hproj : ((projectiveQuadric A).card : ℂ) =
      ∑ P : PrimeProjective p, if quadraticValue A P.rep = 0 then 1 else 0 := by
    simp [projectiveQuadric]
  have hf0 : f 0 = 1 := by simp [f, quadraticValue]
  have hray := sum_nonzero_eq_sum_projective (K := ZMod p) f
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  simp only [f, quadraticValue_units_zero_iff] at hray
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card_units,
    Nat.cast_sub hp1, Nat.cast_one] at hray
  rw [haff, Fintype.sum_eq_add_sum_subtype_ne f 0, hf0, hray, hproj,
    Finset.mul_sum]

end QuaternaryQuadraticForms
