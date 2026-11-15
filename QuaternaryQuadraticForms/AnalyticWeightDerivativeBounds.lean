import QuaternaryQuadraticForms.AnalyticWeightPieces
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Uniform bounds on actual coordinate derivatives

The source family condition uses the coordinate partial derivatives.
The operator-norm formulation used in internal calculus estimates is
proved equivalent by evaluating multilinear derivatives on the standard
Euclidean basis. No stronger family hypothesis is introduced.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators ContDiff

private def multilinearCoordinateMap (k : ℕ) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => RealVector4) ℂ) →ₗ[ℝ]
      ((Fin k → Fin 4) → ℂ) where
  toFun D I := D (fun j => EuclideanSpace.single (I j) (1 : ℝ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem multilinearCoordinateMap_injective (k : ℕ) :
    Function.Injective (multilinearCoordinateMap k) := by
  intro D E h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin k => (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis)
  intro I
  have hI : D (fun j => EuclideanSpace.single (I j) (1 : ℝ)) =
      E (fun j => EuclideanSpace.single (I j) (1 : ℝ)) := congrFun h I
  simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hI

private theorem multilinear_norm_le_coordinate_bound (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ D : ContinuousMultilinearMap ℝ (fun _ : Fin k => RealVector4) ℂ,
        ∀ C : ℝ, 0 ≤ C →
          (∀ I : Fin k → Fin 4,
            ‖D (fun j => EuclideanSpace.single (I j) (1 : ℝ))‖ ≤ C) →
          ‖D‖ ≤ K * C := by
  letI : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => RealVector4) ℂ) :=
    FiniteDimensional.of_injective (multilinearCoordinateMap k)
      (multilinearCoordinateMap_injective k)
  obtain ⟨K, hK, hanti⟩ := (multilinearCoordinateMap k).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (multilinearCoordinateMap_injective k))
  refine ⟨(K : ℝ), hK, ?_⟩
  intro D C hC hbound
  have hnorm : ‖D‖ ≤ (K : ℝ) * ‖multilinearCoordinateMap k D‖ := by
    simpa only [map_zero, dist_zero_right] using hanti.le_mul_dist D 0
  apply hnorm.trans
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  exact (pi_norm_le_iff_of_nonneg hC).mpr hbound

/-- Uniform coordinate partial bounds imply uniform operator-norm bounds
at every order. The conversion constant depends only on that order. -/
theorem UniformCoordinateDerivatives.uniformWeightDerivatives
    {𝒲 : Set (RealVector4 → ℂ)} (h𝒲 : UniformCoordinateDerivatives 𝒲) :
    UniformWeightDerivatives 𝒲 := by
  intro k
  obtain ⟨K, hK, hnorm⟩ := multilinear_norm_le_coordinate_bound k
  obtain ⟨C, hC, hbound⟩ := h𝒲 k
  refine ⟨K * C, mul_pos hK hC, ?_⟩
  intro W hW x
  exact hnorm (iteratedFDeriv ℝ k W x) C hC.le (hbound W hW x)

/-- Evaluating on standard unit vectors recovers the literal coordinate
partial bounds from the operator-norm condition. -/
theorem UniformWeightDerivatives.uniformCoordinateDerivatives
    {𝒲 : Set (RealVector4 → ℂ)} (h𝒲 : UniformWeightDerivatives 𝒲) :
    UniformCoordinateDerivatives 𝒲 := by
  intro k
  obtain ⟨C, hC, hbound⟩ := h𝒲 k
  refine ⟨C, hC, ?_⟩
  intro W hW x I
  have h := (iteratedFDeriv ℝ k W x).le_opNorm
    (fun j => EuclideanSpace.single (I j) (1 : ℝ))
  have hcoord : ‖weightCoordinateDerivative k I W x‖ ≤ ‖iteratedFDeriv ℝ k W x‖ := by
    simpa only [weightCoordinateDerivative, EuclideanSpace.norm_single, norm_one,
      Finset.prod_const_one, mul_one] using h
  exact hcoord.trans (hbound W hW x)

/-- Using operator-norm derivatives in the analytic estimates preserves
the source's family hypothesis exactly. -/
theorem uniformCoordinateDerivatives_iff_uniformWeightDerivatives
    (𝒲 : Set (RealVector4 → ℂ)) :
    UniformCoordinateDerivatives 𝒲 ↔ UniformWeightDerivatives 𝒲 :=
  ⟨UniformCoordinateDerivatives.uniformWeightDerivatives,
    UniformWeightDerivatives.uniformCoordinateDerivatives⟩

/-- A fixed positive scale of the actual product bump has bounded
derivatives of every order, uniformly over all its translates. -/
theorem heathBrownTheta_uniform_translate_derivatives (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y x : RealVector4,
      ‖iteratedFDeriv ℝ k
        (fun z : RealVector4 => (heathBrownTheta (δ⁻¹ • (z - y)) : ℂ)) x‖ ≤ C := by
  let g : RealVector4 → ℂ := fun z => (heathBrownTheta (δ⁻¹ • z) : ℂ)
  have hg : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp
      (heathBrownTheta_contDiff.comp (contDiff_const.smul contDiff_id))
  have hcompact : HasCompactSupport g := by
    have heq : g = localizedWeight (fun _ => 1) δ 0 := by
      funext z
      simp only [g, localizedWeight, sub_zero, one_mul]
    rw [heq]
    exact localizedWeight_hasCompactSupport (fun _ => 1) δ hδ 0
  have hcont : Continuous (iteratedFDeriv ℝ k g) :=
    ContDiff.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) hg
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    (hcompact.iteratedFDeriv k)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y x
  change ‖iteratedFDeriv ℝ k (fun z => g (z - y)) x‖ ≤ max C 1
  rw [iteratedFDeriv_comp_sub]
  exact (hC (x - y)).trans (le_max_left _ _)

/-- Localization at a fixed positive scale preserves uniform bounds on
all derivatives. The constants are chosen before both the original
weight and the centre of the piece. -/
theorem UniformWeightDerivatives.localizedWeight
    {𝒲 : Set (RealVector4 → ℂ)} (h𝒲 : UniformWeightDerivatives 𝒲)
    (hsmooth : ∀ W ∈ 𝒲, ContDiff ℝ ∞ W) (δ : ℝ) (hδ : 0 < δ) :
    UniformWeightDerivatives
      {V | ∃ W ∈ 𝒲, ∃ y : RealVector4, V = localizedWeight W δ y} := by
  classical
  choose A hA hboundA using h𝒲
  choose B hB hboundB using heathBrownTheta_uniform_translate_derivatives δ hδ
  intro k
  let C : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (k - i)).le
  refine ⟨C + 1, by linarith, ?_⟩
  rintro V ⟨W, hW, y, rfl⟩ x
  have htheta : ContDiff ℝ ∞
      (fun z : RealVector4 => (heathBrownTheta (δ⁻¹ • (z - y)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (heathBrownTheta_contDiff.comp (contDiff_const.smul (contDiff_id.sub contDiff_const)))
  have hproduct := norm_iteratedFDeriv_mul_le (hsmooth W hW) htheta x
    (n := k) (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  change ‖iteratedFDeriv ℝ k
    (fun z => W z * (heathBrownTheta (δ⁻¹ • (z - y)) : ℂ)) x‖ ≤ C + 1
  apply hproduct.trans
  apply (show _ ≤ C from ?_).trans (le_add_of_nonneg_right zero_le_one)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hboundA i W hW x) (Nat.cast_nonneg _))
    (hboundB (k - i) y x) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (hA i).le)

/-- The source coordinate-partial family condition is preserved by the
actual localized weights at fixed scale. -/
theorem UniformCoordinateDerivatives.localizedWeight
    {𝒲 : Set (RealVector4 → ℂ)} (h𝒲 : UniformCoordinateDerivatives 𝒲)
    (hsmooth : ∀ W ∈ 𝒲, ContDiff ℝ ∞ W) (δ : ℝ) (hδ : 0 < δ) :
    UniformCoordinateDerivatives
      {V | ∃ W ∈ 𝒲, ∃ y : RealVector4, V = localizedWeight W δ y} :=
  (h𝒲.uniformWeightDerivatives.localizedWeight hsmooth δ hδ).uniformCoordinateDerivatives

/-- Precomposing a uniformly bounded family with any collection of real
linear isometries preserves the same operator-norm derivative bounds. -/
theorem UniformWeightDerivatives.comp_realIsometry
    {𝒲 : Set (RealVector4 → ℂ)} (h𝒲 : UniformWeightDerivatives 𝒲) :
    UniformWeightDerivatives
      {V | ∃ W ∈ 𝒲, ∃ e : RealVector4 ≃ₗᵢ[ℝ] RealVector4, V = W ∘ e} := by
  intro k
  obtain ⟨C, hC, hbound⟩ := h𝒲 k
  refine ⟨C, hC, ?_⟩
  rintro V ⟨W, hW, e, rfl⟩ x
  rw [e.norm_iteratedFDeriv_comp_right]
  exact hbound W hW (e x)

/-- In particular the literal coordinate-partial bounds remain uniform
after all the signed coordinate changes used in the source argument. -/
theorem UniformCoordinateDerivatives.comp_realIsometry
    {𝒲 : Set (RealVector4 → ℂ)} (h𝒲 : UniformCoordinateDerivatives 𝒲) :
    UniformCoordinateDerivatives
      {V | ∃ W ∈ 𝒲, ∃ e : RealVector4 ≃ₗᵢ[ℝ] RealVector4, V = W ∘ e} :=
  h𝒲.uniformWeightDerivatives.comp_realIsometry.uniformCoordinateDerivatives

end QuaternaryQuadraticForms
