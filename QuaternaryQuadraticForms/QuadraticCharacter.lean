import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Integer and complex quadratic characters

The quadratic character in the manuscript takes the integer values `0`, `1`,
and `-1`.  The Fourier sums are complex-valued.  This file makes their
identification explicit by composing mathlib's actual quadratic character
with the canonical homomorphism from the integers to the complex numbers.
The character is extended by zero at zero in both codomains.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The quadratic character of the prime field, viewed as a complex character. -/
def complexQuadraticChar (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- Its value is the cast of the integer-valued quadratic character. -/
@[simp]
theorem complexQuadraticChar_apply (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    complexQuadraticChar p x = (quadraticChar (ZMod p) x : ℂ) := rfl

/-- The complex character retains the three quadratic-character values. -/
theorem complexQuadraticChar_isQuadratic (p : ℕ) [Fact p.Prime] :
    (complexQuadraticChar p).IsQuadratic :=
  (quadraticChar_isQuadratic (F := ZMod p)).comp (Int.castRingHom ℂ)

/-- The square is the principal character, including its zero-extension. -/
theorem complexQuadraticChar_sq (p : ℕ) [Fact p.Prime] :
    complexQuadraticChar p ^ 2 = 1 :=
  (complexQuadraticChar_isQuadratic p).sq_eq_one

/-- At an odd prime the complex quadratic character is nonprincipal. -/
theorem complexQuadraticChar_ne_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    complexQuadraticChar p ≠ 1 := by
  change (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) ≠ 1
  rw [MulChar.ringHomComp_ne_one_iff (show Function.Injective (Int.castRingHom ℂ) from
    Int.cast_injective)]
  exact quadraticChar_ne_one ((ZMod.ringChar_zmod_n p).substr hp)

/-- On an integral input this is exactly the manuscript's Legendre symbol. -/
theorem complexQuadraticChar_intCast (p : ℕ) [Fact p.Prime] (a : ℤ) :
    complexQuadraticChar p (a : ZMod p) = (legendreSym p a : ℂ) := rfl

end QuaternaryQuadraticForms
