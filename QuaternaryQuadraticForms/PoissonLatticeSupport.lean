import QuaternaryQuadraticForms.PoissonDefinitions
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact support on the actual integer lattice

Compact support gives a literal finite set of integer vectors. This also
justifies the source weighted zero sum before any summation identity is used.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A compactly supported function is nonzero at only finitely many integer points. -/
theorem compactSupport_integerRealVector_finite (g : RealVector4 → ℂ)
    (hg : HasCompactSupport g) :
    (Function.support (fun x : Fin 4 → ℤ => g (integerRealVector x))).Finite := by
  obtain ⟨R, hR⟩ := hg.isBounded.exists_norm_le
  apply (integerEuclideanBall R).finite_toSet.subset
  intro x hx
  apply (mem_integerEuclideanBall R x).mpr
  exact hR (integerRealVector x) (subset_tsupport g hx)

/-- Dilation of a compactly supported weight still leaves finitely many lattice points. -/
theorem scaledWeight_integerRealVector_finite (w : RealVector4 → ℂ)
    (hw : HasCompactSupport w) (B : ℝ) (hB : 0 < B) :
    (Function.support (fun x : Fin 4 → ℤ => w (B⁻¹ • integerRealVector x))).Finite := by
  obtain ⟨R, hR⟩ := hw.isBounded.exists_norm_le
  apply (integerEuclideanBall (B * R)).finite_toSet.subset
  intro x hx
  apply (mem_integerEuclideanBall (B * R) x).mpr
  have hb := hR (B⁻¹ • integerRealVector x) (subset_tsupport w hx)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)] at hb
  have h := mul_le_mul_of_nonneg_left hb hB.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul] using h

/-- The literal weighted zero sum has finite support on the integer lattice. -/
theorem weightedQuadraticZeroSum_finite_support
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (w : RealVector4 → ℂ) (hw : HasCompactSupport w) :
    (Function.support (fun x : Fin 4 → ℤ => if integralQuadraticValue A x = 0 then
      w (B⁻¹ • integerRealVector x) * compositeWeight ξ q x else 0)).Finite := by
  apply (scaledWeight_integerRealVector_finite w hw B hB).subset
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

/-- Every test function is supported on the same finite set of integer points. -/
theorem poissonTestFunction_integerRealVector_finite
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (hB : 0 < B)
    (w : RealVector4 → ℂ) (hw : HasCompactSupport w) (c : ℕ+) :
    (Function.support (fun x : Fin 4 → ℤ =>
      poissonTestFunction A B Q w c (integerRealVector x))).Finite := by
  apply (scaledWeight_integerRealVector_finite w hw B hB).subset
  intro x hx
  exact left_ne_zero_of_mul (show
    w (B⁻¹ • integerRealVector x) * _ ≠ 0 from hx)

/-- The total-family representation is exactly the original source weighted sum. -/
theorem weightedQuadraticZeroSum_extend_eq_source (N q : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (hqN : q.Coprime N) (A : Matrix (Fin 4) (Fin 4) ℤ)
    (B : ℝ) (w : RealVector4 → ℂ) :
    weightedQuadraticZeroSum (extendPrimeWeights N ξ) q A B w =
      sourceQuadraticZeroSum N ξ q hqN A B w := by
  simp only [weightedQuadraticZeroSum, sourceQuadraticZeroSum,
    compositeWeight_extend_eq_source N q ξ hqN]

end QuaternaryQuadraticForms
