import QuaternaryQuadraticForms.PolynomialBoxDefinitions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-!
# Actual Euclidean balls in the integer lattice

The source norm is the Euclidean norm.  We use the standard `EuclideanSpace`
norm after casting the four integer coordinates to real numbers.  The finite
ball is cut out from the exact coordinate box with endpoints `-floor U` and
`floor U`; its membership theorem removes this finite representation.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The Euclidean norm of an actual integer four-vector. -/
def integerEuclideanNorm (u : Fin 4 → ℤ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => (u i : ℝ)) : EuclideanSpace ℝ (Fin 4))‖

/-- The source norm has the usual sum-of-squares expression. -/
theorem integerEuclideanNorm_eq_sqrt (u : Fin 4 → ℤ) :
    integerEuclideanNorm u = Real.sqrt (∑ i, (u i : ℝ) ^ 2) := by
  rw [integerEuclideanNorm, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

/-- Euclidean radii are nonnegative. -/
theorem integerEuclideanNorm_nonneg (u : Fin 4 → ℤ) :
    0 ≤ integerEuclideanNorm u := norm_nonneg _

/-- Every coordinate is bounded by the actual Euclidean norm. -/
theorem coordinate_abs_le_integerEuclideanNorm (u : Fin 4 → ℤ) (i : Fin 4) :
    |(u i : ℝ)| ≤ integerEuclideanNorm u := by
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun j => (u j : ℝ))) i

/-- The zero vector is exactly the vector with zero Euclidean norm. -/
theorem integerEuclideanNorm_eq_zero_iff (u : Fin 4 → ℤ) :
    integerEuclideanNorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    have hi := coordinate_abs_le_integerEuclideanNorm u i
    rw [h] at hi
    have hz : (u i : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
    exact_mod_cast hz
  · intro h
    subst u
    simp [integerEuclideanNorm]
    rfl

/-- A nonzero integer vector has Euclidean norm at least one. -/
theorem one_le_integerEuclideanNorm (u : Fin 4 → ℤ) (hu : u ≠ 0) :
    1 ≤ integerEuclideanNorm u := by
  have hi : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨i, hi⟩ := hi
  have hz : (1 : ℤ) ≤ |u i| := by
    have hp := abs_pos.mpr hi
    omega
  have hr : (1 : ℝ) ≤ |(u i : ℝ)| := by exact_mod_cast hz
  exact hr.trans (coordinate_abs_le_integerEuclideanNorm u i)

/-- A positive radius is equivalent to a nonzero integer vector. -/
theorem integerEuclideanNorm_pos_iff (u : Fin 4 → ℤ) :
    0 < integerEuclideanNorm u ↔ u ≠ 0 := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, h⟩ hz
    exact h ((integerEuclideanNorm_eq_zero_iff u).mpr hz).symm
  · intro h
    exact ⟨integerEuclideanNorm_nonneg u,
      Ne.symm (mt (integerEuclideanNorm_eq_zero_iff u).mp h)⟩

/-- Euclidean boundedness puts every coordinate in the exact integer box. -/
theorem integerEuclideanNorm_le_mem_box (U : ℝ) (u : Fin 4 → ℤ)
    (hu : integerEuclideanNorm u ≤ U) :
    u ∈ integerPolynomialBox (fun _ => -⌊U⌋) (fun _ => ⌊U⌋) := by
  apply (mem_integerPolynomialBox _ _ _).mpr
  intro i
  have habs : |(u i : ℝ)| ≤ U :=
    (coordinate_abs_le_integerEuclideanNorm u i).trans hu
  obtain ⟨hl, hr⟩ := abs_le.mp habs
  constructor
  · have hh : -u i ≤ ⌊U⌋ := Int.le_floor.mpr (by simp only [Int.cast_neg]; linarith)
    omega
  · exact Int.le_floor.mpr hr

/-- The finite set of all integer points in a closed Euclidean ball. -/
def integerEuclideanBall (U : ℝ) : Finset (Fin 4 → ℤ) := by
  classical
  exact (integerPolynomialBox (fun _ => -⌊U⌋) (fun _ => ⌊U⌋)).filter
    fun u => integerEuclideanNorm u ≤ U

/-- Membership is exactly the source's Euclidean radius condition. -/
theorem mem_integerEuclideanBall (U : ℝ) (u : Fin 4 → ℤ) :
    u ∈ integerEuclideanBall U ↔ integerEuclideanNorm u ≤ U := by
  classical
  simp only [integerEuclideanBall, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨integerEuclideanNorm_le_mem_box U u h, h⟩⟩

/-- Larger real radii contain every point of a smaller ball. -/
theorem integerEuclideanBall_mono {U V : ℝ} (hUV : U ≤ V) :
    integerEuclideanBall U ⊆ integerEuclideanBall V := by
  intro u hu
  exact (mem_integerEuclideanBall V u).mpr
    (((mem_integerEuclideanBall U u).mp hu).trans hUV)

/-- Each coordinate interval contains at most `3 U` integers for `U ≥ 1`. -/
theorem integerEuclideanInterval_card_le_three_mul (U : ℝ) (hU : 1 ≤ U) :
    ((Finset.Icc (-⌊U⌋) ⌊U⌋).card : ℝ) ≤ 3 * U := by
  have hf : 0 ≤ ⌊U⌋ := Int.floor_nonneg.mpr (by linarith)
  have hc := Int.card_Icc_of_le (-⌊U⌋) ⌊U⌋ (show -⌊U⌋ ≤ ⌊U⌋ + 1 by omega)
  have hc' : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card : ℝ) = (⌊U⌋ : ℝ) + 1 - (-⌊U⌋ : ℤ) := by
    exact_mod_cast hc
  rw [hc']
  have hb := Int.floor_le U
  push_cast
  linarith

end QuaternaryQuadraticForms
