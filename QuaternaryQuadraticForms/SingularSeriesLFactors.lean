import QuaternaryQuadraticForms.SourceDirichletCharacter
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The original character's real-axis Euler factors

The analytic continuation `LFunction` is used at the boundary one. The
Euler-product theorems are applied only strictly inside the half-plane of
absolute convergence. The inverse product at exponent two is justified by
the proved nonvanishing theorem in that half-plane.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped BigOperators Topology

/-- The factor `1 - χ(p) p^(-s)` for the original supplied character. -/
def dirichletRealEulerFactor (M : ℕ) (χ : DirichletCharacter ℂ M)
    (p : Nat.Primes) (s : ℝ) : ℂ :=
  1 - χ ((p : ℕ) : ZMod M) * (↑(((p : ℕ) : ℝ) ^ (-s)) : ℂ)

/-- The real-power normalization agrees with mathlib's complex Euler factor. -/
theorem dirichletRealEulerFactor_eq_cpow (M : ℕ) (χ : DirichletCharacter ℂ M)
    (p : Nat.Primes) (s : ℝ) :
    dirichletRealEulerFactor M χ p s =
      1 - χ ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  simp only [dirichletRealEulerFactor,
    Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)), Complex.ofReal_neg,
    Complex.ofReal_natCast]

/-- The same local factor in reciprocal-power notation. -/
theorem dirichletRealEulerFactor_eq_div (M : ℕ) (χ : DirichletCharacter ℂ M)
    (p : Nat.Primes) (s : ℝ) :
    dirichletRealEulerFactor M χ p s =
      1 - χ ((p : ℕ) : ZMod M) / (↑(((p : ℕ) : ℝ) ^ s) : ℂ) := by
  simp only [dirichletRealEulerFactor, Real.rpow_neg (Nat.cast_nonneg (p : ℕ)),
    Complex.ofReal_inv, div_eq_mul_inv]

/-- Every denominator used at a prime is nonzero, including at exponent one. -/
theorem dirichletRealEulerFactor_ne_zero (M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) (p : Nat.Primes) (s : ℝ) (hs : 1 ≤ s) :
    dirichletRealEulerFactor M χ p s ≠ 0 := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hr : ((p : ℕ) : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hn : ‖χ ((p : ℕ) : ZMod M) * (↑(((p : ℕ) : ℝ) ^ (-s)) : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
      (χ.norm_le_one _)).trans_lt hr
  intro heq
  have heq' := (sub_eq_zero.mp heq).symm
  rw [heq', norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- Each local Euler factor is continuous on the real axis. -/
theorem continuous_dirichletRealEulerFactor (M : ℕ) (χ : DirichletCharacter ℂ M)
    (p : Nat.Primes) : Continuous (dirichletRealEulerFactor M χ p) := by
  have hp : (((p : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact continuous_const.sub (continuous_const.mul
    (Complex.continuous_ofReal.comp ((Real.continuous_const_rpow hp).comp continuous_neg)))

/-- The reciprocal Euler product agrees with the original character's
analytic L-function wherever the real exponent is greater than one. -/
theorem hasProd_inv_dirichletRealEulerFactor (M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) (s : ℝ) (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => (dirichletRealEulerFactor M χ p s)⁻¹)
      (χ.LFunction (s : ℂ)) := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  simpa only [dirichletRealEulerFactor_eq_cpow, χ.LFunction_eq_LSeries hsC]
    using χ.LSeries_eulerProduct_hasProd hsC

/-- The analytic L-function is nonzero in the absolutely convergent region. -/
theorem LFunction_real_ne_zero (M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) (s : ℝ) (hs : 1 < s) :
    χ.LFunction (s : ℂ) ≠ 0 := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  rw [χ.LFunction_eq_LSeries hsC]
  exact χ.LSeries_ne_zero_of_one_lt_re hsC

/-- Inversion is applied to the nonzero L-value, not to an unproved
nonzero singular series or bad-prime density. -/
theorem hasProd_dirichletRealEulerFactor (M : ℕ) [NeZero M]
    (χ : DirichletCharacter ℂ M) (s : ℝ) (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => dirichletRealEulerFactor M χ p s)
      (χ.LFunction (s : ℂ))⁻¹ := by
  have h := hasProd_inv_dirichletRealEulerFactor M χ s hs
  have hi := Filter.Tendsto.inv₀ h (LFunction_real_ne_zero M χ s hs)
  simpa only [Finset.prod_inv_distrib, inv_inv] using hi

end QuaternaryQuadraticForms
