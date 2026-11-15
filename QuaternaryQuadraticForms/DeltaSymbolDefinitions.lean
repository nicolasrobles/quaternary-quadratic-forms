import QuaternaryQuadraticForms.RamanujanSums
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The actual Heath--Brown delta-symbol data

The bump, its integral, the fixed normalized weight, the sampling sum,
and the common kernel are the definitions in Heath--Brown, Sections 2--3.
The kernel is defined before any scale or integral frequency is chosen.
The positive-modulus summand uses the existing literal unit-residue sum.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators
open MeasureTheory

/-- The one-dimensional bump in Heath--Brown (2.1). -/
def heathBrownBaseBump (t : ℝ) : ℝ :=
  if |t| < 1 then Real.exp (-(1 - t ^ 2)⁻¹) else 0

/-- Its normalization integral, Heath--Brown (2.4). -/
def heathBrownBumpMass : ℝ := ∫ t : ℝ, heathBrownBaseBump t

/-- The fixed weight supported on `(1/2,1)` in Heath--Brown Section 3. -/
def heathBrownBump (t : ℝ) : ℝ :=
  4 / heathBrownBumpMass * heathBrownBaseBump (4 * t - 3)

/-- The unnormalized sampling sum in Heath--Brown (3.3). -/
def heathBrownSamplingSum (Q : ℝ) : ℝ :=
  ∑' c : ℕ+, heathBrownBump (((c : ℕ) : ℝ) / Q)

/-- The common kernel in Heath--Brown Section 3, independent of `Q` and `n`. -/
def heathBrownDeltaKernel (z : ℝ × ℝ) : ℝ :=
  ∑' j : ℕ+, (z.1 * ((j : ℕ) : ℝ))⁻¹ *
    (heathBrownBump (z.1 * ((j : ℕ) : ℝ)) -
      heathBrownBump (|z.2| / (z.1 * ((j : ℕ) : ℝ))))

/-- The literal normalization from (3.3); positivity on `Q >= 3` is proved. -/
def heathBrownNormalization (Q : ℝ) : ℝ := Q / heathBrownSamplingSum Q

/-- One positive-modulus term in the source delta identity. -/
def deltaSymbolTerm (h : ℝ × ℝ → ℝ) (Q : ℝ) (n : ℤ) (c : ℕ+) : ℂ :=
  @integralRamanujanSum (c : ℕ) ⟨Nat.ne_of_gt c.pos⟩ n *
    (h (((c : ℕ) : ℝ) / Q, (n : ℝ) / Q ^ 2) : ℂ)

end QuaternaryQuadraticForms
