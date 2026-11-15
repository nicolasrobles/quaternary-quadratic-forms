import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform normalization of a fixed delta-method bump

The sampling sum is finite at every positive real scale.  On the source
range `Q >= 3`, one sample lies in the fixed compact interval
`[7/12, 11/12]` inside the positive part of the bump.  This supplies a
uniform positive lower bound without assuming that the normalization is
bounded on the larger admissible range near `Q = 2`.

The final estimate is an internal deduction from a raw sampling estimate.
This module contains no literature premise.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal positive-integer sampling sum of a fixed real bump. -/
def bumpSamplingSum (ω : ℝ → ℝ) (Q : ℝ) : ℝ :=
  ∑' c : ℕ+, ω ((c : ℝ) / Q)

/-- A bump vanishing at and above one has finitely many nonzero samples
at every positive real scale. -/
theorem bumpSamplingSum_finite_support (ω : ℝ → ℝ)
    (hzero : ∀ x : ℝ, 1 ≤ x → ω x = 0) (Q : ℝ) (hQ : 0 < Q) :
    (Function.support (fun c : ℕ+ => ω ((c : ℝ) / Q))).Finite := by
  have hfinite : (PNat.val ⁻¹' Set.Iic (Nat.ceil Q)).Finite :=
    (Set.finite_Iic (Nat.ceil Q)).preimage PNat.coe_injective.injOn
  refine hfinite.subset ?_
  intro c hc
  change (c : ℕ) ≤ Nat.ceil Q
  by_contra hle
  have hnat : Nat.ceil Q < (c : ℕ) := lt_of_not_ge hle
  have hreal : (Nat.ceil Q : ℝ) < (c : ℝ) := by exact_mod_cast hnat
  have hQc : Q ≤ (c : ℝ) := (Nat.le_ceil Q).trans hreal.le
  exact hc (hzero _ ((le_div_iff₀ hQ).mpr (by simpa using hQc)))

/-- Summability follows from the explicit finite support, independently
of any Poisson summation or asymptotic estimate. -/
theorem bumpSamplingSum_summable (ω : ℝ → ℝ)
    (hzero : ∀ x : ℝ, 1 ≤ x → ω x = 0) (Q : ℝ) (hQ : 0 < Q) :
    Summable (fun c : ℕ+ => ω ((c : ℝ) / Q)) :=
  summable_of_finite_support (bumpSamplingSum_finite_support ω hzero Q hQ)

/-- A continuous nonnegative bump that is positive on `(1/2,1)` has
a uniform positive sampling sum for every real `Q >= 3`.  The lower
bound is chosen before the scale. -/
theorem bumpSamplingSum_uniform_pos (ω : ℝ → ℝ)
    (hcontinuous : Continuous ω) (hnonneg : ∀ x : ℝ, 0 ≤ ω x)
    (hpositive : ∀ x : ℝ, 1 / 2 < x → x < 1 → 0 < ω x)
    (hzero : ∀ x : ℝ, 1 ≤ x → ω x = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ Q : ℝ, 3 ≤ Q → d ≤ bumpSamplingSum ω Q := by
  obtain ⟨d, hd, hbound⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (7 / 12 : ℝ) (11 / 12))).exists_forall_le'
      hcontinuous.continuousOn (a := 0) (by
        intro x hx
        exact hpositive x (by linarith [hx.1]) (by linarith [hx.2]))
  refine ⟨d, hd, ?_⟩
  intro Q hQ
  have hQpos : 0 < Q := by linarith
  let a : ℝ := 3 * Q / 4 + 1 / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hfloor : (Nat.floor a : ℝ) ≤ a := Nat.floor_le ha
  have hlt : a < (Nat.floor a : ℝ) + 1 := Nat.lt_floor_add_one a
  have hnat : 0 < Nat.floor a := by
    have hreal : (0 : ℝ) < Nat.floor a := by dsimp [a] at hlt; linarith
    exact_mod_cast hreal
  let c : ℕ+ := ⟨Nat.floor a, hnat⟩
  have hleft : (7 / 12 : ℝ) ≤ (c : ℝ) / Q := by
    apply (le_div_iff₀ hQpos).mpr
    change (7 / 12 : ℝ) * Q ≤ (Nat.floor a : ℝ)
    dsimp [a] at hlt
    linarith
  have hright : (c : ℝ) / Q ≤ (11 / 12 : ℝ) := by
    apply (div_le_iff₀ hQpos).mpr
    change (Nat.floor a : ℝ) ≤ (11 / 12 : ℝ) * Q
    dsimp [a] at hfloor
    linarith
  calc
    d ≤ ω ((c : ℝ) / Q) := hbound _ ⟨hleft, hright⟩
    _ ≤ bumpSamplingSum ω Q :=
      (bumpSamplingSum_summable ω hzero Q hQpos).le_tsum c
        (fun b _ => hnonneg _)

/-- Uniform rapid approximation of `Q / S(Q)` follows from the raw
sampling error of order `j+1`.  Its constant is independent of every
real scale `Q >= 3`. -/
theorem bumpNormalization_error_bound (ω : ℝ → ℝ)
    (hcontinuous : Continuous ω) (hnonneg : ∀ x : ℝ, 0 ≤ ω x)
    (hpositive : ∀ x : ℝ, 1 / 2 < x → x < 1 → 0 < ω x)
    (hzero : ∀ x : ℝ, 1 ≤ x → ω x = 0)
    (hraw : ∀ m : ℕ, 2 ≤ m → ∃ A : ℝ, 0 < A ∧
      ∀ Q : ℝ, 1 < Q →
        |bumpSamplingSum ω Q - Q| ≤ A * Q / Q ^ m)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      |Q / bumpSamplingSum ω Q - 1| ≤ C / Q ^ j := by
  obtain ⟨d, hd, hbound⟩ :=
    bumpSamplingSum_uniform_pos ω hcontinuous hnonneg hpositive hzero
  obtain ⟨A, hA, hrawA⟩ := hraw (j + 1) (Nat.succ_le_succ hj)
  refine ⟨A / d, div_pos hA hd, ?_⟩
  intro Q hQ
  have hQpos : 0 < Q := by linarith
  have hsum : 0 < bumpSamplingSum ω Q := hd.trans_le (hbound Q hQ)
  calc
    |Q / bumpSamplingSum ω Q - 1| =
        |bumpSamplingSum ω Q - Q| / bumpSamplingSum ω Q := by
      rw [div_sub_one hsum.ne', abs_div, abs_of_pos hsum, abs_sub_comm]
    _ ≤ (A * Q / Q ^ (j + 1)) / bumpSamplingSum ω Q :=
      div_le_div_of_nonneg_right (hrawA Q (by linarith)) hsum.le
    _ ≤ (A * Q / Q ^ (j + 1)) / d :=
      div_le_div_of_nonneg_left (by positivity) hd (hbound Q hQ)
    _ = (A / d) / Q ^ j := by
      rw [pow_succ]
      field_simp

end QuaternaryQuadraticForms
