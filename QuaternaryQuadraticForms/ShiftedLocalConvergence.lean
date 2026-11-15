import QuaternaryQuadraticForms.ShiftedLocalDefinitions
import QuaternaryQuadraticForms.LocalDensityConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Absolute convergence and boundary continuity of the shifted local factors

Every shifted coefficient on the nonnegative real axis is bounded by its
unshifted absolute value. The already proved summable majorant therefore
applies at every prime, including every exceptional prime.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open Filter
open scoped BigOperators Topology

/-- Nonnegative shifts give damping of norm at most one at every prime. -/
theorem shiftedLocalDensity_damping_norm_le_one (p : ℕ) [Fact p.Prime]
    (z : ℝ) (hz : 0 ≤ z) :
    ‖(((p : ℝ) ^ (-z) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (neg_nonpos.mpr hz)

/-- The absolute values of the actual unshifted local coefficients uniformly
dominate all nonnegative shifts. -/
theorem shiftedLocalDensityTerm_norm_le (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (z : ℝ) (hz : 0 ≤ z) (k : ℕ) :
    ‖shiftedLocalDensityTerm p A z k‖ ≤ ‖localDensityTerm p A k‖ := by
  rw [shiftedLocalDensityTerm, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (shiftedLocalDensity_damping_norm_le_one p z hz))

/-- Absolute convergence at every prime, uniformly dominated for `z ≥ 0`. -/
theorem summable_norm_shiftedLocalDensityTerm (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 ≤ z) :
    Summable (fun k : ℕ => ‖shiftedLocalDensityTerm p A z k‖) :=
  (summable_norm_localDensityTerm p A hA hdet).of_nonneg_of_le
    (fun k => norm_nonneg (shiftedLocalDensityTerm p A z k))
    (fun k => shiftedLocalDensityTerm_norm_le p A z hz k)

/-- The literal shifted local series is summable at every prime. -/
theorem summable_shiftedLocalDensityTerm (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (z : ℝ) (hz : 0 ≤ z) :
    Summable (shiftedLocalDensityTerm p A z) :=
  (summable_norm_shiftedLocalDensityTerm p A hA hdet z hz).of_norm

/-- Each prime-power coefficient is continuous in the real shift. -/
theorem continuous_shiftedLocalDensityTerm (p : ℕ) [NeZero p]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (k : ℕ) :
    Continuous (fun z : ℝ => shiftedLocalDensityTerm p A z k) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  exact continuous_const.mul
    ((Complex.continuous_ofReal.comp
      ((Real.continuous_const_rpow hp).comp continuous_neg)).pow k)

/-- Summable domination proves continuity of the actual local factor on the
closed nonnegative half-line, including its boundary point zero. -/
theorem continuousOn_shiftedLocalDensity (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    ContinuousOn (shiftedLocalDensity p A) (Set.Ici 0) := by
  exact continuousOn_tsum
    (fun k => (continuous_shiftedLocalDensityTerm p A k).continuousOn)
    (summable_norm_localDensityTerm p A hA hdet)
    (fun k z hz => shiftedLocalDensityTerm_norm_le p A z hz k)

/-- At zero shift the local series equals the actual density defined by
normalized counts, with no assumption that this density is nonzero. -/
@[simp] theorem shiftedLocalDensity_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    shiftedLocalDensity p A 0 = (localQuadraticDensity p A : ℂ) := by
  simpa [shiftedLocalDensity] using (hasSum_localDensityTerm p A hA hdet).tsum_eq

/-- The right boundary limit is the actual counting density at every prime. -/
theorem tendsto_shiftedLocalDensity_zero (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0) :
    Tendsto (shiftedLocalDensity p A) (𝓝[Set.Ici 0] 0)
      (𝓝 (localQuadraticDensity p A : ℂ)) := by
  simpa only [shiftedLocalDensity_zero p A hA hdet] using
    ((continuousOn_shiftedLocalDensity p A hA hdet) 0
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)).tendsto

end QuaternaryQuadraticForms
