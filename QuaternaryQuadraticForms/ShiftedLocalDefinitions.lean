import QuaternaryQuadraticForms.LocalDensityDefinitions
import QuaternaryQuadraticForms.CompleteSumSpecializations
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The local complete-sum series with a real shift

The shift multiplies the actual prime-power coefficient by `p^(-k*z)`.
The normalization lemma identifies this definition with the prime-power
factor of the global Dirichlet series, including the coefficient at one.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The actual prime-power complete-sum coefficient with a real shift. -/
def shiftedLocalDensityTerm (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (k : ℕ) : ℂ :=
  localDensityTerm p A k * ((((p : ℝ) ^ (-z) : ℝ) : ℂ) ^ k)

/-- The shifted local factor, defined by its actual prime-power coefficients. -/
def shiftedLocalDensity (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) : ℂ :=
  ∑' k : ℕ, shiftedLocalDensityTerm p A z k

/-- The coefficient of the zeroth prime power is one at every shift. -/
@[simp] theorem shiftedLocalDensityTerm_zero_exponent (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) :
    shiftedLocalDensityTerm p A z 0 = 1 := by
  simp [shiftedLocalDensityTerm, localDensityTerm, unweightedCompleteSum_one]

/-- At shift zero, each local coefficient is the existing density coefficient. -/
@[simp] theorem shiftedLocalDensityTerm_zero_shift (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (k : ℕ) :
    shiftedLocalDensityTerm p A 0 k = localDensityTerm p A k := by
  simp [shiftedLocalDensityTerm]

/-- The geometric definition uses exactly the `4 + z` normalization of the
global complete-sum Dirichlet series. -/
theorem shiftedLocalDensityTerm_eq_primePower (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (k : ℕ) :
    shiftedLocalDensityTerm p A z k =
      unweightedCompleteSum (p ^ k) A 0 /
        (((((p ^ k : ℕ) : ℝ) ^ (4 + z)) : ℝ) : ℂ) := by
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hden : (((((p ^ k : ℕ) : ℝ) ^ (4 + z)) : ℝ) : ℂ) =
      (p : ℂ) ^ (4 * k) * ((((p : ℝ) ^ z : ℝ) : ℂ) ^ k) := by
    rw [Nat.cast_pow, ← Real.rpow_pow_comm hp.le, Real.rpow_add hp,
      Real.rpow_ofNat, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_pow, Complex.ofReal_natCast, pow_mul]
    simp only [Complex.ofReal_pow]
  rw [shiftedLocalDensityTerm, localDensityTerm, hden,
    Real.rpow_neg hp.le, Complex.ofReal_inv, inv_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A shifted reciprocal power separates into its integral power and damping
factor; the equality keeps the real-power convention explicit. -/
theorem div_natCast_rpow_nat_add (p : ℕ) [NeZero p] (w : ℂ)
    (n : ℕ) (z : ℝ) :
    w / ((((p : ℝ) ^ ((n : ℝ) + z) : ℝ)) : ℂ) =
      (w / (p : ℂ) ^ n) * ((((p : ℝ) ^ (-z) : ℝ)) : ℂ) := by
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [Real.rpow_add hp, Real.rpow_natCast, Real.rpow_neg hp.le,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_inv]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end QuaternaryQuadraticForms
