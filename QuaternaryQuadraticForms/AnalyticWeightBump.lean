import QuaternaryQuadraticForms.AnalyticDefinitions
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linarith

/-!
# The literal smooth bump used in the source weight decomposition

The fixed one-dimensional source bump is identified with mathlib's
proved smooth exponential cutoff. Its positivity, compact support and
positive normalization integral are internal proofs.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory
open scoped BigOperators ContDiff

/-- The source bump is exactly the standard flat exponential cutoff. -/
theorem heathBrownBaseBump_eq_expNegInvGlue (t : ℝ) :
    heathBrownBaseBump t = expNegInvGlue (1 - t ^ 2) := by
  by_cases ht : |t| < 1
  · have hpos : 0 < 1 - t ^ 2 :=
      sub_pos.mpr ((sq_lt_one_iff_abs_lt_one t).mpr ht)
    simp [heathBrownBaseBump, expNegInvGlue, ht, not_le.mpr hpos]
  · have hnonpos : 1 - t ^ 2 ≤ 0 :=
      sub_nonpos.mpr (le_of_not_gt (fun h => ht ((sq_lt_one_iff_abs_lt_one t).mp h)))
    simp [heathBrownBaseBump, expNegInvGlue, ht, hnonpos]

/-- Infinite differentiability is the library's smooth order, with no
analyticity claim at the support boundary. -/
theorem heathBrownBaseBump_contDiff : ContDiff ℝ ∞ heathBrownBaseBump := by
  have heq : heathBrownBaseBump = fun t : ℝ => expNegInvGlue (1 - t ^ 2) :=
    funext heathBrownBaseBump_eq_expNegInvGlue
  rw [heq]
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

/-- The fixed source bump is nonnegative. -/
theorem heathBrownBaseBump_nonneg (t : ℝ) : 0 ≤ heathBrownBaseBump t := by
  rw [heathBrownBaseBump_eq_expNegInvGlue]
  exact expNegInvGlue.nonneg _

/-- The exact nonzero set of the source bump is the open unit interval. -/
theorem heathBrownBaseBump_ne_zero_iff (t : ℝ) :
    heathBrownBaseBump t ≠ 0 ↔ |t| < 1 := by
  rw [heathBrownBaseBump_eq_expNegInvGlue, ne_eq,
    expNegInvGlue.zero_iff_nonpos, not_le, sub_pos, sq_lt_one_iff_abs_lt_one]

/-- The source bump has its actual compact support in the closed unit
interval. -/
theorem heathBrownBaseBump_hasCompactSupport : HasCompactSupport heathBrownBaseBump := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))
  intro t ht
  have h := (heathBrownBaseBump_ne_zero_iff t).mp ht
  exact ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

/-- The literal normalization integral is an integral of an integrable
function, rather than a default value assigned to a divergent integral. -/
theorem heathBrownBaseBump_integrable : Integrable heathBrownBaseBump :=
  heathBrownBaseBump_contDiff.continuous.integrable_of_hasCompactSupport
    heathBrownBaseBump_hasCompactSupport

/-- The source normalizing mass is strictly positive. -/
theorem heathBrownBumpMass_pos : 0 < heathBrownBumpMass := by
  unfold heathBrownBumpMass
  apply heathBrownBaseBump_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    heathBrownBaseBump_hasCompactSupport heathBrownBaseBump_nonneg
  apply (heathBrownBaseBump_ne_zero_iff 0).mpr
  norm_num

/-- The literal four-dimensional source bump is nonnegative. -/
theorem heathBrownTheta_nonneg (x : RealVector4) : 0 ≤ heathBrownTheta x := by
  apply mul_nonneg (pow_nonneg (inv_nonneg.mpr heathBrownBumpMass_pos.le) 4)
  exact Finset.prod_nonneg (fun i _ => heathBrownBaseBump_nonneg (x i))

/-- The source product bump is jointly infinitely differentiable in its
four Euclidean coordinates. -/
theorem heathBrownTheta_contDiff : ContDiff ℝ ∞ heathBrownTheta := by
  unfold heathBrownTheta
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact heathBrownBaseBump_contDiff.comp (contDiff_piLp_apply 2)

/-- A nonzero product bump forces every coordinate into the open unit
interval. -/
theorem heathBrownTheta_coordinates_lt_one (x : RealVector4)
    (hx : heathBrownTheta x ≠ 0) (i : Fin 4) : |x i| < 1 := by
  classical
  have hprod : (∏ j : Fin 4, heathBrownBaseBump (x j)) ≠ 0 :=
    (mul_ne_zero_iff.mp hx).2
  exact (heathBrownBaseBump_ne_zero_iff (x i)).mp
    ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))

/-- The closed source support is contained in the actual coordinate cube. -/
theorem heathBrownTheta_tsupport_subset_cube :
    tsupport heathBrownTheta ⊆ {x : RealVector4 | ∀ i : Fin 4, |x i| ≤ 1} := by
  have hclosed : IsClosed {x : RealVector4 | ∀ i : Fin 4, |x i| ≤ 1} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le
      (show Continuous (fun x : RealVector4 => |x i|) from
        (show ContDiff ℝ ∞ (fun x : RealVector4 => x i) from
          contDiff_piLp_apply 2).continuous.abs) continuous_const
  apply closure_minimal _ hclosed
  intro x hx i
  exact (heathBrownTheta_coordinates_lt_one x hx i).le

private theorem realVector4_norm_le_two_of_coordinates (x : RealVector4)
    (h : ∀ i : Fin 4, |x i| ≤ 1) : ‖x‖ ≤ 2 := by
  have hs : ‖x‖ ^ 2 ≤ 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i : Fin 4, ‖x i‖ ^ 2) ≤ ∑ _i : Fin 4, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs, sq_abs] using
          (sq_le_one_iff_abs_le_one (x i)).mpr (h i)
      _ = 4 := by norm_num
  nlinarith [norm_nonneg x]

/-- The source cube has Euclidean radius two in four variables. -/
theorem heathBrownTheta_norm_le_two_of_mem_tsupport (x : RealVector4)
    (hx : x ∈ tsupport heathBrownTheta) : ‖x‖ ≤ 2 :=
  realVector4_norm_le_two_of_coordinates x
    (heathBrownTheta_tsupport_subset_cube hx)

/-- The literal product bump has compact Euclidean support. -/
theorem heathBrownTheta_hasCompactSupport : HasCompactSupport heathBrownTheta := by
  apply (isCompact_closedBall (0 : RealVector4) 2).of_isClosed_subset
    (isClosed_tsupport heathBrownTheta)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    heathBrownTheta_norm_le_two_of_mem_tsupport x hx

/-- The product bump is integrable with respect to canonical Euclidean
Lebesgue measure. -/
theorem heathBrownTheta_integrable : Integrable heathBrownTheta :=
  heathBrownTheta_contDiff.continuous.integrable_of_hasCompactSupport
    heathBrownTheta_hasCompactSupport

/-- Fubini and the volume-preserving Euclidean coordinate equivalence give
the exact source normalization, including the power four. -/
theorem heathBrownTheta_integral : (∫ x : RealVector4, heathBrownTheta x) = 1 := by
  have hprod : (∫ x : RealVector4, ∏ i : Fin 4, heathBrownBaseBump (x i)) =
      heathBrownBumpMass ^ 4 := by
    calc
      _ = ∫ x : Fin 4 → ℝ, ∏ i : Fin 4, heathBrownBaseBump (x i) :=
        (EuclideanSpace.volume_preserving_measurableEquiv (Fin 4)).integral_comp' _
      _ = _ := by
        simpa only [Fintype.card_fin, heathBrownBumpMass] using
          (integral_fintype_prod_volume_eq_pow (ι := Fin 4) heathBrownBaseBump)
  unfold heathBrownTheta
  rw [integral_const_mul, hprod, ← mul_pow,
    inv_mul_cancel₀ heathBrownBumpMass_pos.ne', one_pow]

end QuaternaryQuadraticForms
