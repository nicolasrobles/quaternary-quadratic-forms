import QuaternaryQuadraticForms.PoissonLatticeSupport
import QuaternaryQuadraticForms.DeltaSymbolTheorem
import QuaternaryQuadraticForms.RealQuadraticGeometry

/-!
# Arithmetic identities for insertion of the delta symbol

The integer n is exactly the quotient F(x)/q on the cone congruence.
The kernel argument and the additive phase retain their original values.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The real quadratic form agrees with the actual integral form on the lattice. -/
theorem realQuadraticValue_integerRealVector
    (A : Matrix (Fin 4) (Fin 4) ℤ) (x : Fin 4 → ℤ) :
    realQuadraticValue (A.map (Int.castRingHom ℝ)) (integerRealVector x) =
      (integralQuadraticValue A x : ℝ) := by
  simp [realQuadraticValue, integerRealVector, integralQuadraticValue,
    dotProduct, Matrix.mulVec]

/-- The exact scaled quadratic value at an integer point. -/
theorem realQuadraticValue_scaled_integerRealVector
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (x : Fin 4 → ℤ) :
    realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • integerRealVector x) =
      (integralQuadraticValue A x : ℝ) / B ^ 2 := by
  rw [realQuadraticValue_smul, realQuadraticValue_integerRealVector]
  simp only [inv_pow, div_eq_mul_inv, mul_comm]

/-- With Q=B/sqrt(q), the source second kernel coordinate is exactly n/Q². -/
theorem poisson_delta_scaled_argument (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (x : Fin 4 → ℤ) (n : ℤ) (hn : integralQuadraticValue A x = (q : ℤ) * n) :
    realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • integerRealVector x) =
      (n : ℝ) / (B / Real.sqrt (q : ℝ)) ^ 2 := by
  rw [realQuadraticValue_scaled_integerRealVector, hn]
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hs : Real.sqrt (q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  push_cast
  rw [div_pow, Real.sq_sqrt hq.le]
  field_simp

/-- Cancelling q in the phase gives the original unit character modulo c. -/
theorem poisson_delta_phase (q c : ℕ) [NeZero q] [NeZero c]
    (a n : ℤ) :
    ZMod.stdAddChar (N := q * c) ((a * ((q : ℤ) * n) : ℤ) : ZMod (q * c)) =
      ZMod.stdAddChar (N := c) ((a * n : ℤ) : ZMod c) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  field_simp

/-- The actual integer summand, summed over the original unit residues. -/
def poissonDeltaLatticeTerm
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (x : Fin 4 → ℤ) : ℂ :=
  ∑ a : (ZMod (c : ℕ))ˣ,
    mixedIntegerSummand ξ q (c : ℕ) A 0 (((a : ZMod (c : ℕ)).val : ℕ) : ℤ) x *
      poissonTestFunction A B Q w c (integerRealVector x)

/-- Outside the scaled weight support the entire unit sum vanishes. -/
theorem poissonDeltaLatticeTerm_eq_zero_of_weight_eq_zero
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (x : Fin 4 → ℤ) (hx : w (B⁻¹ • integerRealVector x) = 0) :
    poissonDeltaLatticeTerm ξ q A B Q w c x = 0 := by
  simp [poissonDeltaLatticeTerm, poissonTestFunction, hx]

/-- On the cone congruence the unit sum is the exact delta-symbol summand. -/
theorem poissonDeltaLatticeTerm_eq_of_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (w : RealVector4 → ℂ) (c : ℕ+) (x : Fin 4 → ℤ)
    (n : ℤ) (hn : integralQuadraticValue A x = (q : ℤ) * n) :
    poissonDeltaLatticeTerm ξ q A B (B / Real.sqrt (q : ℝ)) w c x =
      (w (B⁻¹ • integerRealVector x) * compositeWeight ξ q x) *
        deltaSymbolTerm heathBrownDeltaKernel (B / Real.sqrt (q : ℝ)) n c := by
  have hdiv : (q : ℤ) ∣ integralQuadraticValue A x := ⟨n, hn⟩
  rw [poissonDeltaLatticeTerm, deltaSymbolTerm_eq_unit_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mixedIntegerSummand, if_pos hdiv, zero_dotProduct, add_zero,
    poissonTestFunction, poisson_delta_scaled_argument q A B hB x n hn]
  rw [hn, poisson_delta_phase]
  have ha : (((((a : ZMod (c : ℕ)).val : ℕ) : ℤ) * n : ℤ) : ZMod (c : ℕ)) =
      (a : ZMod (c : ℕ)) * (n : ZMod (c : ℕ)) := by
    simp
  rw [ha]
  ring

/-- Off the cone congruence every mixed summand is zero. -/
theorem poissonDeltaLatticeTerm_eq_zero_of_not_dvd
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (x : Fin 4 → ℤ) (hx : ¬(q : ℤ) ∣ integralQuadraticValue A x) :
    poissonDeltaLatticeTerm ξ q A B Q w c x = 0 := by
  simp [poissonDeltaLatticeTerm, mixedIntegerSummand, hx]

end QuaternaryQuadraticForms
