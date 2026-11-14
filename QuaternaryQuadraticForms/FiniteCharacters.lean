import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Fintype.BigOperators

/-!
# Additive character sums along a finite-field ray

The sums below use the actual unit group of a finite field.  In the prime-field
specialization, `ZMod.stdAddChar` is the standard complex exponential occurring
in the manuscript.  These are the individual-ray evaluations used in (4.5).
-/

open scoped BigOperators

namespace QuaternaryQuadraticForms

/-- Removing the zero term from a primitive additive-character sum leaves the
finite-field cardinality minus one at zero frequency, and minus one otherwise. -/
theorem primitiveAddChar_units_sum
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar K R) (hψ : ψ.IsPrimitive) (c : K) :
    (∑ t : Kˣ, ψ ((t : K) * c)) =
      if c = 0 then (Fintype.card K : R) - 1 else -1 := by
  classical
  have hsplit :
      (∑ x : K, ψ (x * c)) = 1 + ∑ t : Kˣ, ψ ((t : K) * c) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun x : K ↦ ψ (x * c)) 0]
    simp only [zero_mul, AddChar.map_zero_eq_one]
    congr 1
    exact (Equiv.sum_comp unitsEquivNeZero (fun x : {x : K // x ≠ 0} ↦
      ψ ((x : K) * c))).symm
  have hsum := AddChar.sum_mulShift c hψ
  rw [hsplit] at hsum
  split_ifs with hc
  · rw [if_pos hc] at hsum
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsum)
  · rw [if_neg hc] at hsum
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hsum)

/-- The standard additive character on the prime field has the ray sum used in
equation (4.5) of the frozen manuscript. -/
theorem stdAddChar_units_sum (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (∑ t : (ZMod p)ˣ, ZMod.stdAddChar ((t : ZMod p) * c)) =
      if c = 0 then (p : ℂ) - 1 else -1 := by
  simpa only [ZMod.card] using
    primitiveAddChar_units_sum (ZMod.stdAddChar (N := p))
      (ZMod.isPrimitive_stdAddChar p) c

end QuaternaryQuadraticForms
