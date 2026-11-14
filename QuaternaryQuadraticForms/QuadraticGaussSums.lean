import QuaternaryQuadraticForms.CompleteSums

/-!
# The actual quadratic Gauss sums at positive moduli

The residue-ring definition uses the matrix quadratic value and the standard
positive additive character. The integral definition reduces the manuscript's
matrix, scalar, and frequency into the same finite sum.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal four-variable quadratic Gauss sum over a residue ring. -/
def quadraticGaussSum (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) (ZMod n)) (a : ZMod n)
    (u : Fin 4 → ZMod n) : ℂ :=
  ∑ x : Fin 4 → ZMod n,
    ZMod.stdAddChar (a * dotProduct x (A.mulVec x) + dotProduct u x)

/-- The same Gauss sum for the manuscript's integral data. -/
def integralQuadraticGaussSum (n : ℕ) [NeZero n]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (a : ℤ) (u : Fin 4 → ℤ) : ℂ :=
  quadraticGaussSum n (A.map (Int.castRingHom (ZMod n))) (a : ZMod n)
    (fun i => (u i : ZMod n))

end QuaternaryQuadraticForms
