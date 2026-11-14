import QuaternaryQuadraticForms.RamanujanSums
import QuaternaryQuadraticForms.CRTArithmetic
import Mathlib.Data.Nat.Totient

/-!
# Multiplicativity and zero frequency of the actual Ramanujan sums

The source's scaled CRT equivalence on actual residue units splits the
standard additive character into its two factors. Thus the literal
Ramanujan sum is multiplicative, including factors equal to one.
At zero frequency it is the cardinality of the actual unit group.
The shared-factor totient identity needed on the dual cone is also
proved, with the source's divisibility condition and no squarefreeness
or nonvanishing assumption on a character sum.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem ramanujan_scaled_unit_phase (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (t : ℤ) (a : (ZMod m)ˣ) (b : (ZMod n)ˣ) :
    ZMod.stdAddChar
        (((scaledChineseRemainderUnits m n h (a, b) : (ZMod (m * n))ˣ) :
          ZMod (m * n)) * (t : ZMod (m * n))) =
      ZMod.stdAddChar ((a : ZMod m) * (t : ZMod m)) *
        ZMod.stdAddChar ((b : ZMod n) * (t : ZMod n)) := by
  rw [scaledChineseRemainderUnits_apply]
  have hphase :
      ((n : ZMod (m * n)) * ((a : ZMod m).val : ZMod (m * n)) +
        (m : ZMod (m * n)) * ((b : ZMod n).val : ZMod (m * n))) *
          (t : ZMod (m * n)) =
      (((n : ℤ) * (((a : ZMod m).val : ℤ) * t) +
        (m : ℤ) * (((b : ZMod n).val : ℤ) * t) : ℤ) : ZMod (m * n)) := by
    push_cast
    ring
  rw [hphase, stdAddChar_crt_split]
  simp

/-- Multiplicativity of the literal integral Ramanujan sum, proved by
the actual reduced-residue CRT bijection. Both moduli may equal one. -/
theorem integralRamanujanSum_mul (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (t : ℤ) :
    integralRamanujanSum (m * n) t =
      integralRamanujanSum m t * integralRamanujanSum n t := by
  classical
  simp only [integralRamanujanSum, residueRamanujanSum]
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        ZMod.stdAddChar
          (((scaledChineseRemainderUnits m n h ab : (ZMod (m * n))ˣ) :
            ZMod (m * n)) * (t : ZMod (m * n))) :=
      (Equiv.sum_comp (scaledChineseRemainderUnits m n h)
        (fun a : (ZMod (m * n))ˣ =>
          ZMod.stdAddChar ((a : ZMod (m * n)) * (t : ZMod (m * n))))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      simp_rw [ramanujan_scaled_unit_phase m n h t]

/-- At zero frequency the actual Ramanujan sum is the Euler totient,
including the single unit and single character value at modulus one. -/
theorem integralRamanujanSum_zero (n : ℕ) [NeZero n] :
    integralRamanujanSum n 0 = (Nat.totient n : ℂ) := by
  simp [integralRamanujanSum, residueRamanujanSum, AddChar.map_zero_eq_one]

/-- A divisor of the modulus multiplies its totient by that same factor.
This applies to the source factor `gcd(q,c)` and also includes zero cases. -/
theorem totient_mul_of_dvd (d c : ℕ) (h : d ∣ c) :
    Nat.totient (d * c) = d * Nat.totient c := by
  by_cases hd : d = 0
  · simp [hd]
  have hmul := Nat.totient_gcd_mul_totient_mul d c
  rw [Nat.gcd_eq_left h, mul_assoc] at hmul
  simpa [(Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd)).ne', mul_comm] using hmul

end QuaternaryQuadraticForms
