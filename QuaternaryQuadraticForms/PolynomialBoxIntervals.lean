import QuaternaryQuadraticForms.PolynomialBoxDefinitions
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Arbitrary intervals in the polynomial box theorem

A finite integer interval is exactly a closed interval with integer endpoints.
The same applies to the integer points of any real interval, including open,
closed, and half-open intervals.  Empty intervals are retained.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- Every finite order-connected set of integers is a closed integer interval. -/
theorem integerInterval_eq_Icc (I : Finset ℤ) (hI : (I : Set ℤ).OrdConnected) :
    ∃ a b : ℤ, I = Finset.Icc a b := by
  by_cases h : I.Nonempty
  · refine ⟨I.min' h, I.max' h, ?_⟩
    ext z
    constructor
    · intro hz
      exact Finset.mem_Icc.mpr ⟨I.min'_le z hz, I.le_max' z hz⟩
    · intro hz
      exact hI.out (I.min'_mem h) (I.max'_mem h) (Finset.mem_Icc.mp hz)
  · refine ⟨1, 0, ?_⟩
    have h0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [h0, Finset.Icc_eq_empty_of_lt (by decide : (0 : ℤ) < 1)]

/-- The integer points of a real interval form an integer interval. -/
theorem realInterval_integer_points_ordConnected (I : Set ℝ) (hI : I.OrdConnected) :
    ((fun z : ℤ => (z : ℝ)) ⁻¹' I).OrdConnected := by
  apply hI.preimage_mono
  intro a b hab
  exact Int.cast_le.mpr hab

/-- A real interval with finitely many integer points has exact integer endpoints
for those points.  No endpoint openness convention is required. -/
theorem realInterval_integer_points_eq_Icc (I : Set ℝ) (hI : I.OrdConnected)
    (hfin : ((fun z : ℤ => (z : ℝ)) ⁻¹' I).Finite) :
    ∃ a b : ℤ, hfin.toFinset = Finset.Icc a b := by
  apply integerInterval_eq_Icc
  simpa only [Set.Finite.coe_toFinset] using
    realInterval_integer_points_ordConnected I hI

/-- The endpoint representation agrees with literal membership in the given real interval. -/
theorem realInterval_integer_membership_Icc (I : Set ℝ) (hI : I.OrdConnected)
    (hfin : ((fun z : ℤ => (z : ℝ)) ⁻¹' I).Finite) :
    ∃ a b : ℤ, ∀ z : ℤ, (z : ℝ) ∈ I ↔ a ≤ z ∧ z ≤ b := by
  obtain ⟨a, b, hab⟩ := realInterval_integer_points_eq_Icc I hI hfin
  refine ⟨a, b, fun z => ?_⟩
  have hmem : z ∈ hfin.toFinset ↔ z ∈ Finset.Icc a b := by rw [hab]
  simpa only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_Icc] using hmem

end QuaternaryQuadraticForms
