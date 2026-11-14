import QuaternaryQuadraticForms.WeightedGaussSums
import QuaternaryQuadraticForms.PrimePowerResidues
import QuaternaryQuadraticForms.GaussNorm
import QuaternaryQuadraticForms.FourierRays

/-!
# Actual residue digits for weighted quadratic Gauss sums

At a modulus `m * p` with `p ∣ m`, the final residue digit enters the
quadratic phase linearly and does not change the weight modulo `p`.
Additive orthogonality then selects exactly the stationary residues.
The digit identity itself does not require primality or nonsingularity.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem weighted_quadratic_add_symmetric
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (x y : Fin 4 → ℤ) :
    integralQuadraticValue A (x + y) = integralQuadraticValue A x +
      2 * dotProduct x (A.mulVec y) + integralQuadraticValue A y := by
  have hcross : dotProduct y (A.mulVec x) = dotProduct x (A.mulVec y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  simp only [integralQuadraticValue, Matrix.mulVec_add, add_dotProduct,
    dotProduct_add]
  rw [hcross]
  ring

private theorem weightedGauss_digit_phase_intCast (p m : ℕ) (hpm : p ∣ m)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (a : ℤ) (u y z : Fin 4 → ℤ) :
    ((a * integralQuadraticValue A (fun i => y i + (m : ℤ) * z i) +
      dotProduct u (fun i => y i + (m : ℤ) * z i) : ℤ) : ZMod (m * p)) =
      ((a * integralQuadraticValue A y + dotProduct u y +
        (m : ℤ) * dotProduct ((2 * a) • A.mulVec y + u) z : ℤ) : ZMod (m * p)) := by
  obtain ⟨t, ht⟩ := hpm
  have hvec : (fun i => y i + (m : ℤ) * z i) = y + (m : ℤ) • z := rfl
  have hcross : dotProduct (A.mulVec y) z = dotProduct y (A.mulVec z) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA,
      dotProduct_comm]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨-(a * (t : ℤ) * integralQuadraticValue A z), ?_⟩
  rw [hvec, weighted_quadratic_add_symmetric A hA]
  rw [show integralQuadraticValue A ((m : ℤ) • z) =
      (m : ℤ) ^ 2 * integralQuadraticValue A z from integralQuadraticValue_mul A m z]
  simp only [Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
    add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hcross, ht]
  push_cast
  ring

/-- The actual final residue digit contributes only the gradient phase. -/
theorem weightedGauss_digit_phase (p m : ℕ) [NeZero p] [NeZero m] (hpm : p ∣ m)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (a : ℤ) (u y z : Fin 4 → ℤ) :
    ZMod.stdAddChar (N := m * p)
      ((a * integralQuadraticValue A (fun i => y i + (m : ℤ) * z i) +
        dotProduct u (fun i => y i + (m : ℤ) * z i) : ℤ) : ZMod (m * p)) =
      ZMod.stdAddChar (N := m * p)
        ((a * integralQuadraticValue A y + dotProduct u y : ℤ) : ZMod (m * p)) *
      ZMod.stdAddChar (N := p)
        ((dotProduct ((2 * a) • A.mulVec y + u) z : ℤ) : ZMod p) := by
  rw [weightedGauss_digit_phase_intCast p m hpm A hA, Int.cast_add,
    AddChar.map_add_eq_mul]
  congr 1
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp

private theorem weightedGauss_digit_weight (p m : ℕ) (hpm : p ∣ m)
    (y z : Fin 4 → ℤ) :
    reduceFrequency p (fun i => y i + (m : ℤ) * z i) = reduceFrequency p y := by
  have hm : ((m : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hpm)
  ext i
  simp only [reduceFrequency, Int.cast_add, Int.cast_mul, hm, zero_mul, add_zero]

private theorem weightedGauss_digit_orthogonality (p : ℕ) [NeZero p]
    (g : Fin 4 → ℤ) :
    (∑ z : Fin 4 → ZMod p,
      ZMod.stdAddChar (N := p) ((dotProduct g (residueLift p z) : ℤ) : ZMod p)) =
        if reduceFrequency p g = 0 then (p : ℂ) ^ 4 else 0 := by
  have hphase (z : Fin 4 → ZMod p) :
      ((dotProduct g (residueLift p z) : ℤ) : ZMod p) =
        dotProduct (reduceFrequency p g) z := by
    simp [dotProduct, reduceFrequency, residueLift]
  simp_rw [hphase]
  exact stdAddChar_residue_vector_orthogonality p (reduceFrequency p g)

/-- Actual two-digit reindexing and orthogonality restrict the weighted sum
to the residues where `2 a A y + u` vanishes modulo `p`. -/
theorem weightedIntegralGaussSum_stationary_expansion (p m : ℕ)
    [NeZero p] [NeZero m] (hpm : p ∣ m)
    (ξ : (Fin 4 → ZMod p) → ℂ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (a : ℤ) (u : Fin 4 → ℤ) :
    weightedIntegralGaussSum p (m * p) ξ A a u =
      ∑ y : Fin 4 → ZMod m,
        ξ (reduceFrequency p (residueLift m y)) *
          ZMod.stdAddChar (N := m * p)
            ((a * integralQuadraticValue A (residueLift m y) +
              dotProduct u (residueLift m y) : ℤ) : ZMod (m * p)) *
          (if reduceFrequency p ((2 * a) • A.mulVec (residueLift m y) + u) = 0
            then (p : ℂ) ^ 4 else 0) := by
  classical
  change (∑ x : Fin 4 → ZMod (m * p),
    (fun v => ξ (reduceFrequency p v) * ZMod.stdAddChar (N := m * p)
      ((a * integralQuadraticValue A v + dotProduct u v : ℤ) : ZMod (m * p)))
        (residueLift (m * p) x)) = _
  rw [sum_residueLift_digits m p (fun v => ξ (reduceFrequency p v) *
    ZMod.stdAddChar (N := m * p)
      ((a * integralQuadraticValue A v + dotProduct u v : ℤ) : ZMod (m * p)))]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [weightedGauss_digit_weight p m hpm,
    weightedGauss_digit_phase p m hpm A hA a u, ← mul_assoc, ← Finset.mul_sum]
  rw [weightedGauss_digit_orthogonality]

end QuaternaryQuadraticForms
