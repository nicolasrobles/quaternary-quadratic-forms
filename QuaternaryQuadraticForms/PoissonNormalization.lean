import QuaternaryQuadraticForms.PoissonDefinitions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# The scalar normalization in Lemma 5.1

The delta coefficient Q^(-2), four-dimensional Jacobian B^4, and residue
lattice factor q^(-4) combine exactly to B^2 q^(-3).
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The exact scalar identity with Q=B/sqrt(q); the numerator k is arbitrary. -/
theorem poisson_normalization_factor (q : ℕ) [NeZero q]
    (B : ℝ) (hB : 0 < B) (k : ℝ) :
    ((k / (B / Real.sqrt (q : ℝ)) ^ 2 : ℝ) : ℂ) *
        ((B : ℂ) ^ 4 / (q : ℂ) ^ 4) =
      ((k * B ^ 2 / (q : ℝ) ^ 3 : ℝ) : ℂ) := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  push_cast
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

end QuaternaryQuadraticForms
