import QuaternaryQuadraticForms.IntegralGaussSums
import Mathlib.Topology.Order.Basic

/-!
# The literal local quadratic densities

The finite counts use every residue vector modulo the indicated prime power,
including the origin. The local density is the limit of their normalized real
counts. Its existence and equality with the complete-sum series are proved in
the subsequent modules.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual number of zeros of the integral form modulo `p^k`. -/
def primePowerZeroCount (p k : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Fin 4 → ZMod (p ^ k) =>
    (integralQuadraticValue A (residueLift (p ^ k) x) : ZMod (p ^ k)) = 0)).card

/-- The source normalization `p^(-3k) N_(p,k)` as a real number. -/
def normalizedPrimePowerZeroCount (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (k : ℕ) : ℝ :=
  (primePowerZeroCount p k A : ℝ) / (p : ℝ) ^ (3 * k)

/-- The literal local complete-sum coefficient `S_(p^k)(0)/p^(4k)`. -/
def localDensityTerm (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (k : ℕ) : ℂ :=
  unweightedCompleteSum (p ^ k) A 0 / (p : ℂ) ^ (4 * k)

/-- The local density defined from the actual normalized counting sequence.
Its convergence is established independently, rather than built into this definition. -/
def localQuadraticDensity (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) : ℝ :=
  limUnder Filter.atTop (normalizedPrimePowerZeroCount p A)

end QuaternaryQuadraticForms
