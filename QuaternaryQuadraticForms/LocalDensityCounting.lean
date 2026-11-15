import QuaternaryQuadraticForms.LocalDensityGaussReduction
import QuaternaryQuadraticForms.CompleteSumSpecializations

/-!
# The finite counting identity for the local density

Composite-modulus additive orthogonality counts the actual zeros. The exact
unit/multiple scalar partition then gives the partial-sum identity at every
prime power, including modulus one and the prime two.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Additive orthogonality expresses the actual prime-power zero count through
the full scalar Gauss sum. This holds at every positive base modulus. -/
theorem primePowerZeroCount_additive (p k : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (p : ℂ) ^ k * (primePowerZeroCount p k A : ℂ) =
      ∑ a : ZMod (p ^ k),
        quadraticGaussSum (p ^ k) (A.map (Int.castRingHom _)) a 0 := by
  classical
  have hscalar (c : ZMod (p ^ k)) :
      (∑ a : ZMod (p ^ k), ZMod.stdAddChar (a * c)) =
        if c = 0 then (p : ℂ) ^ k else 0 := by
    simpa only [ZMod.card, apply_ite, Nat.cast_zero, Nat.cast_pow] using
      AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar (p ^ k))
  simp only [quadraticGaussSum, zero_dotProduct, add_zero]
  rw [Finset.sum_comm]
  simp_rw [hscalar, ← integralQuadraticValue_residueLift]
  rw [← Finset.sum_filter]
  simp [primePowerZeroCount, mul_comm]

/-- The normalized count is exactly the full scalar Gauss sum divided by
`p^(4k)`, with all scalar residues retained. -/
theorem normalizedPrimePowerZeroCount_eq_fullGauss (p k : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (normalizedPrimePowerZeroCount p A k : ℂ) =
      (∑ a : ZMod (p ^ k),
        quadraticGaussSum (p ^ k) (A.map (Int.castRingHom _)) a 0) /
        (p : ℂ) ^ (4 * k) := by
  rw [← primePowerZeroCount_additive]
  unfold normalizedPrimePowerZeroCount
  push_cast
  rw [show 4 * k = k + 3 * k by omega, pow_add]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  field_simp

/-- Increasing the exponent appends exactly the next literal complete-sum
coefficient. No regularity or nonsingularity hypothesis enters this identity. -/
theorem normalizedPrimePowerZeroCount_recurrence (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (normalizedPrimePowerZeroCount p A (k + 1) : ℂ) =
      (normalizedPrimePowerZeroCount p A k : ℂ) + localDensityTerm p A (k + 1) := by
  rw [normalizedPrimePowerZeroCount_eq_fullGauss,
    primePower_fullGauss_recurrence, add_div,
    normalizedPrimePowerZeroCount_eq_fullGauss]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcancel (z : ℂ) :
      (p : ℂ) ^ 4 * z / (p : ℂ) ^ (4 * (k + 1)) =
        z / (p : ℂ) ^ (4 * k) := by
    rw [show 4 * (k + 1) = 4 + 4 * k by omega, pow_add]
    field_simp
  rw [hcancel, add_comm]
  rfl

/-- The zero exponent has its single residue vector and source normalization one. -/
theorem normalizedPrimePowerZeroCount_zero (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    normalizedPrimePowerZeroCount p A 0 = 1 := by
  have hzero (x : Fin 4 → ZMod 1) :
      (integralQuadraticValue A (residueLift 1 x) : ZMod 1) = 0 :=
    Subsingleton.elim _ _
  simp [normalizedPrimePowerZeroCount, primePowerZeroCount, hzero]

/-- The exact finite identity in Lemma 3.8: normalized actual zero counts
are partial sums of the literal complete-sum coefficients. Every prime,
including two, and the boundary exponent zero are covered. -/
theorem normalizedPrimePowerZeroCount_eq_sum (p k : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (normalizedPrimePowerZeroCount p A k : ℂ) =
      ∑ j ∈ Finset.range (k + 1), localDensityTerm p A j := by
  induction k with
  | zero =>
      simp [normalizedPrimePowerZeroCount_zero, localDensityTerm,
        unweightedCompleteSum_one]
  | succ k ih =>
      rw [normalizedPrimePowerZeroCount_recurrence, ih]
      exact (Finset.sum_range_succ (localDensityTerm p A) (k + 1)).symm

end QuaternaryQuadraticForms
