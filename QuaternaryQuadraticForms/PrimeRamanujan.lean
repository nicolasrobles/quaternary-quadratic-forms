import QuaternaryQuadraticForms.FiniteCharacters

/-!
# The prime Ramanujan sum

The source sum is the sum of the standard additive character over the
nonzero residue classes. Its two values make invariance under a nonzero
factor explicit, including the zero-frequency case.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal prime Ramanujan sum over nonzero residue classes. -/
def primeRamanujan (p : ℕ) [Fact p.Prime] (c : ZMod p) : ℂ :=
  ∑ s : (ZMod p)ˣ, ZMod.stdAddChar ((s : ZMod p) * c)

/-- The two exact prime Ramanujan values. -/
theorem primeRamanujan_eq (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    primeRamanujan p c = if c = 0 then (p : ℂ) - 1 else -1 :=
  stdAddChar_units_sum p c

/-- Multiplying the argument by a nonzero field element preserves the sum. -/
theorem primeRamanujan_mul (p : ℕ) [Fact p.Prime] (r c : ZMod p) (hr : r ≠ 0) :
    primeRamanujan p (r * c) = primeRamanujan p c := by
  simp only [primeRamanujan_eq, mul_eq_zero, hr, false_or]

/-- Inversion permutes the nonzero residue classes in the Ramanujan sum. -/
theorem primeRamanujan_inverse_sum (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (∑ s : (ZMod p)ˣ, ZMod.stdAddChar ((s : ZMod p)⁻¹ * c)) =
      primeRamanujan p c := by
  simpa only [Equiv.inv_apply, Units.val_inv_eq_inv_val] using
    Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
      (fun s : (ZMod p)ˣ => ZMod.stdAddChar ((s : ZMod p) * c))

/-- The reciprocal phase in a singular pencil member gives exactly the
same Ramanujan value, including when its argument vanishes. -/
theorem primeRamanujan_reciprocal_phase (p : ℕ) [Fact p.Prime]
    (h4 : (4 : ZMod p) ≠ 0) (c : ZMod p) :
    (∑ s : (ZMod p)ˣ, ZMod.stdAddChar (-c / (4 * (s : ZMod p)))) =
      primeRamanujan p c := by
  have hphase (s : (ZMod p)ˣ) :
      -c / (4 * (s : ZMod p)) = (s : ZMod p)⁻¹ * (-(4 : ZMod p)⁻¹ * c) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hphase]
  rw [primeRamanujan_inverse_sum, primeRamanujan_mul p _ c (neg_ne_zero.mpr (inv_ne_zero h4))]

end QuaternaryQuadraticForms
