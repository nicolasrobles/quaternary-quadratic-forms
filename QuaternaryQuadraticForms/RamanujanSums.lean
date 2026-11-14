import QuaternaryQuadraticForms.PrimeRamanujan

/-!
# The actual Ramanujan sums at positive moduli

These are sums of the standard additive character over the unit group.
Multiplication and inversion are reindexed on that group, including the
one-element residue ring. No field assumption is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal Ramanujan sum on a residue-ring frequency. -/
def residueRamanujanSum (n : ℕ) [NeZero n] (m : ZMod n) : ℂ :=
  ∑ a : (ZMod n)ˣ, ZMod.stdAddChar ((a : ZMod n) * m)

/-- The manuscript's Ramanujan sum at an integral frequency. -/
def integralRamanujanSum (n : ℕ) [NeZero n] (m : ℤ) : ℂ :=
  residueRamanujanSum n (m : ZMod n)

/-- Reduction of the actual integer phase gives the same unit sum. -/
theorem integralRamanujanSum_eq_lift_sum (n : ℕ) [NeZero n] (m : ℤ) :
    integralRamanujanSum n m =
      ∑ a : (ZMod n)ˣ,
        ZMod.stdAddChar (((((a : ZMod n).val : ℕ) : ℤ) * m : ℤ) : ZMod n) := by
  simp [integralRamanujanSum, residueRamanujanSum]

/-- At a prime this definition is exactly the previously checked prime sum. -/
theorem residueRamanujanSum_prime (p : ℕ) [Fact p.Prime] (m : ZMod p) :
    residueRamanujanSum p m = primeRamanujan p m := rfl

/-- The unit sum at modulus one has its single term. -/
theorem residueRamanujanSum_modulus_one (m : ZMod 1) :
    residueRamanujanSum 1 m = 1 := by
  have hc (z : ZMod 1) : ZMod.stdAddChar z = (1 : ℂ) := by
    rw [Subsingleton.elim z 0, AddChar.map_zero_eq_one]
  simp [residueRamanujanSum, hc]

/-- The integral Ramanujan sum at modulus one is one at every frequency. -/
theorem integralRamanujanSum_modulus_one (m : ℤ) :
    integralRamanujanSum 1 m = 1 :=
  residueRamanujanSum_modulus_one _

/-- Multiplication of the frequency by an actual unit preserves the sum. -/
theorem residueRamanujanSum_units_mul (n : ℕ) [NeZero n]
    (r : (ZMod n)ˣ) (m : ZMod n) :
    residueRamanujanSum n ((r : ZMod n) * m) = residueRamanujanSum n m := by
  have h := Equiv.sum_comp (Equiv.mulRight r)
    (fun a : (ZMod n)ˣ => ZMod.stdAddChar ((a : ZMod n) * m))
  change (∑ a : (ZMod n)ˣ, ZMod.stdAddChar (((a * r : (ZMod n)ˣ) : ZMod n) * m)) =
    ∑ a : (ZMod n)ˣ, ZMod.stdAddChar ((a : ZMod n) * m) at h
  simpa only [residueRamanujanSum, Units.val_mul, mul_assoc] using h

/-- The unit criterion alone suffices for frequency-scaling invariance. -/
theorem residueRamanujanSum_mul (n : ℕ) [NeZero n]
    (r m : ZMod n) (hr : IsUnit r) :
    residueRamanujanSum n (r * m) = residueRamanujanSum n m := by
  rcases hr with ⟨v, rfl⟩
  exact residueRamanujanSum_units_mul n v m

/-- Inversion permutes the actual unit summation set at every positive modulus. -/
theorem residueRamanujanSum_inverse_sum (n : ℕ) [NeZero n] (m : ZMod n) :
    (∑ a : (ZMod n)ˣ, ZMod.stdAddChar ((a : ZMod n)⁻¹ * m)) =
      residueRamanujanSum n m := by
  simpa only [residueRamanujanSum, Equiv.inv_apply, ZMod.inv_coe_unit] using
    Equiv.sum_comp (Equiv.inv (ZMod n)ˣ)
      (fun a : (ZMod n)ˣ => ZMod.stdAddChar ((a : ZMod n) * m))

/-- Negative reciprocal unit phases give the original Ramanujan sum,
including zero frequency and modulus one. -/
theorem residueRamanujanSum_reciprocal_phase (n : ℕ) [NeZero n]
    (r m : ZMod n) (hr : IsUnit r) :
    (∑ a : (ZMod n)ˣ, ZMod.stdAddChar (-(r * (a : ZMod n))⁻¹ * m)) =
      residueRamanujanSum n m := by
  let v : (ZMod n)ˣ := hr.unit
  have hv : (v : ZMod n) = r := hr.unit_spec
  let e : (ZMod n)ˣ ≃ (ZMod n)ˣ :=
    (Equiv.mulLeft v).trans ((Equiv.inv (ZMod n)ˣ).trans (Equiv.mulLeft (-1)))
  have he (a : (ZMod n)ˣ) : ((e a : (ZMod n)ˣ) : ZMod n) =
      -(r * (a : ZMod n))⁻¹ := by
    change (((-1 : (ZMod n)ˣ) * (v * a)⁻¹ : (ZMod n)ˣ) : ZMod n) = _
    rw [Units.val_mul]
    simp only [Units.val_neg, Units.val_one, neg_one_mul]
    rw [← ZMod.inv_coe_unit, Units.val_mul, hv]
  calc
    _ = ∑ a : (ZMod n)ˣ, ZMod.stdAddChar (((e a : (ZMod n)ˣ) : ZMod n) * m) := by
      simp only [he]
    _ = _ := Equiv.sum_comp e
      (fun a : (ZMod n)ˣ => ZMod.stdAddChar ((a : ZMod n) * m))

end QuaternaryQuadraticForms
