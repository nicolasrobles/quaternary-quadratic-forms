import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Standard additive characters at product moduli

These identities use the actual standard characters on `ZMod`. They apply
to all positive moduli, including one, without a coprimality hypothesis.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Cancelling one factor of the modulus in the numerator of the actual
standard additive character. -/
theorem stdAddChar_mul_modulus (m n : ℕ) [NeZero m] [NeZero n] (z : ℤ) :
    ZMod.stdAddChar (N := m * n) (((n : ℤ) * z : ℤ) : ZMod (m * n)) =
      ZMod.stdAddChar (N := m) (z : ZMod m) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

/-- The source's scaled CRT coordinates split the standard additive phase.
The identity itself holds even when the two moduli are not coprime. -/
theorem stdAddChar_crt_split (m n : ℕ) [NeZero m] [NeZero n] (a b : ℤ) :
    ZMod.stdAddChar (N := m * n)
        (((n : ℤ) * a + (m : ℤ) * b : ℤ) : ZMod (m * n)) =
      ZMod.stdAddChar (N := m) (a : ZMod m) *
        ZMod.stdAddChar (N := n) (b : ZMod n) := by
  rw [Int.cast_add, AddChar.map_add_eq_mul, stdAddChar_mul_modulus]
  congr 1
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

/-- Modulus one contributes the trivial phase, as in the source conventions. -/
theorem stdAddChar_modulus_one (x : ZMod 1) : ZMod.stdAddChar x = 1 := by
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, AddChar.map_zero_eq_one]

end QuaternaryQuadraticForms
