import QuaternaryQuadraticForms.PoissonDefinitions
import QuaternaryQuadraticForms.DeltaSymbolTheorem
import QuaternaryQuadraticForms.RealQuadraticGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Smoothness and finite modulus support of the Poisson test function

The only literature input used here is the already registered source kernel.
Compact support of the original weight gives one modulus cutoff before any
point of Euclidean space or lattice frequency is chosen.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped ContDiff
open MeasureTheory

/-- For every positive scale, the actual Poisson test function is a smooth weight. -/
theorem poissonTestFunction_isSmoothWeight
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (hB : 0 < B) (hQ : 0 < Q) (hw : IsSmoothWeight w) :
    IsSmoothWeight (poissonTestFunction A B Q w c) := by
  have hlin : ContDiff ℝ ∞ (fun x : RealVector4 => B⁻¹ • x) :=
    contDiff_const.smul contDiff_id
  have hF : ContDiff ℝ ∞ (fun x : RealVector4 =>
      realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • x)) :=
    (realQuadraticValue_contDiff _).comp hlin
  have hh : ContDiff ℝ ∞ (fun x : RealVector4 =>
      heathBrownDeltaKernel ((c : ℝ) / Q,
        realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • x))) :=
    heathBrownDeltaKernel_properties.1.comp_contDiff
      (contDiff_const.prodMk hF) (fun _ => div_pos (Nat.cast_pos.mpr c.pos) hQ)
  have hhC := Complex.ofRealCLM.contDiff.comp hh
  have hs : HasCompactSupport (fun x : RealVector4 => w (B⁻¹ • x)) := by
    simpa only [Function.comp_apply, Homeomorph.smul_apply, Units.val_mk0] using
      hw.2.comp_homeomorph (Homeomorph.smul (Units.mk0 B⁻¹ (inv_ne_zero hB.ne')))
  exact ⟨(hw.1.comp hlin).mul hhC, hs.mul_right⟩

/-- One natural modulus cutoff makes the entire test function vanish,
uniformly over its Euclidean argument. -/
theorem poissonTestFunction_eventually_zero
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (w : RealVector4 → ℂ)
    (hQ : 0 < Q) (hw : HasCompactSupport w) :
    ∃ K : ℕ, ∀ c : ℕ+, K < (c : ℕ) → poissonTestFunction A B Q w c = 0 := by
  obtain ⟨M, hM⟩ := hw.bddAbove_image
    (realQuadraticValue_continuous (A.map (Int.castRingHom ℝ))).abs.continuousOn
  refine ⟨⌈Q * max 1 (2 * M)⌉₊, ?_⟩
  intro c hc
  funext x
  change poissonTestFunction A B Q w c x = 0
  by_cases hwx : w (B⁻¹ • x) = 0
  · simp only [poissonTestFunction, hwx, zero_mul]
  · have hx : B⁻¹ • x ∈ tsupport w := subset_tsupport w hwx
    have hvalue : |realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • x)| ≤ M :=
      hM ⟨B⁻¹ • x, hx, rfl⟩
    have hceil : (⌈Q * max 1 (2 * M)⌉₊ : ℝ) < (c : ℝ) := by exact_mod_cast hc
    have hcut : Q * max 1 (2 * M) < (c : ℝ) := (Nat.le_ceil _).trans_lt hceil
    have hbound : Q * max 1
        (2 * |realQuadraticValue (A.map (Int.castRingHom ℝ)) (B⁻¹ • x)|) < (c : ℝ) :=
      (mul_le_mul_of_nonneg_left
        (max_le_max_left 1 (mul_le_mul_of_nonneg_left hvalue (by norm_num))) hQ.le).trans_lt hcut
    rw [poissonTestFunction,
      deltaSymbolKernel_eq_zero_of_modulus_bound heathBrownDeltaKernel
        heathBrownDeltaKernel_properties.2.2 Q hQ c _ hbound]
    simp

/-- The same compact-support cutoff annihilates the actual delta integral
at every frequency, so the positive-modulus expansion is genuinely finite. -/
theorem poissonDeltaIntegral_eventually_zero
    (A : Matrix (Fin 4) (Fin 4) ℤ) (Q : ℝ) (w : RealVector4 → ℂ)
    (hQ : 0 < Q) (hw : HasCompactSupport w) :
    ∃ K : ℕ, ∀ c : ℕ+, K < (c : ℕ) → ∀ v : RealVector4,
      deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
        w ((c : ℝ) / Q) v = 0 := by
  obtain ⟨K, hK⟩ := poissonTestFunction_eventually_zero A 1 Q w hQ hw
  refine ⟨K, ?_⟩
  intro c hc v
  unfold deltaIntegral
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  have hx := congrFun (hK c hc) x
  simp only [poissonTestFunction, inv_one, one_smul, Pi.zero_apply] at hx
  simp only [hx, zero_mul, Pi.zero_apply]

end QuaternaryQuadraticForms
