import QuaternaryQuadraticForms.SingularEulerAbsolute
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

/-!
# Positive-shift agreement with the ordered singular series

The actual real cutoff agrees, in the absolutely convergent range, with the
ordinary sum. This bridges the Euler product to the ordered definition that
will also be used at the boundary shift zero.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped Topology

/-- The zero term is excluded in the manuscript and is also zero in the
totalized summand, so the literal real cutoff is an ordinary initial sum. -/
theorem singularSeriesPartialSum_eq_sum_range (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z X : ℝ) :
    singularSeriesPartialSum q A z X =
      ∑ c ∈ Finset.range (⌊X⌋₊ + 1), singularSeriesTerm q A z c := by
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos ⌊X⌋₊),
    singularSeriesTerm_zero, zero_add]
  change singularSeriesPartialSum q A z X =
    ∑ c ∈ Finset.Ico 1 (⌊X⌋₊ + 1), singularSeriesTerm q A z c
  rw [Finset.Ico_add_one_right_eq_Icc]
  rfl

/-- The difference of two actual cutoffs is the literal finite tail, with
its lower endpoint excluded and upper endpoint included. -/
theorem singularSeriesPartialSum_sub_eq_sum_Ioc (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z X Y : ℝ) (_hX : 1 ≤ X) (hXY : X ≤ Y) :
    singularSeriesPartialSum q A z Y - singularSeriesPartialSum q A z X =
      ∑ c ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, singularSeriesTerm q A z c := by
  simp only [singularSeriesPartialSum_eq_sum_range]
  rw [← Finset.sum_Ico_eq_sub (singularSeriesTerm q A z)
    (Nat.add_le_add_right (Nat.floor_mono hXY) 1), Finset.Ico_add_one_add_one_eq_Ioc]

/-- The finite tail's natural-number interval represents exactly the
manuscript's real inequalities `X < c ≤ Y`. -/
theorem mem_singularSeries_tail_interval (X Y : ℝ) (hX : 1 ≤ X) (hXY : X ≤ Y)
    (c : ℕ) :
    c ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊ ↔ X < (c : ℝ) ∧ (c : ℝ) ≤ Y := by
  simp only [Finset.mem_Ioc, Nat.floor_lt (zero_le_one.trans hX),
    Nat.le_floor_iff (zero_le_one.trans (hX.trans hXY))]

/-- At positive shift the actual real-cutoff partial sums converge to the
absolutely convergent sum used in the Euler product. -/
theorem tendsto_singularSeriesPartialSum_tsum (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 < z) :
    Tendsto (singularSeriesPartialSum q A z) atTop
      (𝓝 (∑' c : ℕ, singularSeriesTerm q A z c)) := by
  have hsum := (summable_singularSeriesTerm q A hA hdet z hz).hasSum.tendsto_sum_nat
  have hcut : Tendsto (fun X : ℝ => ⌊X⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  simpa only [Function.comp_def, ← singularSeriesPartialSum_eq_sum_range] using hsum.comp hcut

/-- The ordered value equals the absolute sum for every positive shift. -/
theorem singularSeriesValue_eq_tsum (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 < z) :
    singularSeriesValue q A z = ∑' c : ℕ, singularSeriesTerm q A z c :=
  (tendsto_singularSeriesPartialSum_tsum q A hA hdet z hz).limUnder_eq

end QuaternaryQuadraticForms
