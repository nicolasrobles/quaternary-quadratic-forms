import QuaternaryQuadraticForms.PoissonAnalytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact Euclidean Fourier scaling in Lemma 5.1

The scalar change of variables is applied to canonical Lebesgue measure.
The frequency calculation retains the source factors q, c, B and sqrt(q).
-/

noncomputable section

namespace QuaternaryQuadraticForms

open MeasureTheory

/-- The four-dimensional Jacobian in the source change of variables. -/
theorem poisson_integral_comp_inv_smul (f : RealVector4 → ℂ)
    (B : ℝ) (hB : 0 ≤ B) :
    (∫ x : RealVector4, f (B⁻¹ • x)) = (B : ℂ) ^ 4 * ∫ x : RealVector4, f x := by
  simpa only [RealVector4, finrank_euclideanSpace_fin,
    Complex.real_smul, Complex.ofReal_pow] using
    Measure.integral_comp_inv_smul_of_nonneg volume f hB

/-- The rescaled Fourier integral equals B^4 times the source delta integral
at frequency r*B*v, for every positive radius r=c/Q. -/
theorem poissonFourierIntegral_testFunction_general
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B Q : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (v : RealVector4) (hB : 0 < B) (hQ : 0 < Q) :
    poissonFourierIntegral (poissonTestFunction A B Q w c) v =
      (B : ℂ) ^ 4 * deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
        w ((c : ℝ) / Q) ((((c : ℝ) / Q) * B) • v) := by
  let r : ℝ := (c : ℝ) / Q
  have hr : r ≠ 0 := (div_pos (Nat.cast_pos.mpr c.pos) hQ).ne'
  let f : RealVector4 → ℂ := fun y => w y *
    (heathBrownDeltaKernel (r, realQuadraticValue (A.map (Int.castRingHom ℝ)) y) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-inner ℝ v (B • y) : ℝ) : ℂ))
  calc
    poissonFourierIntegral (poissonTestFunction A B Q w c) v =
        ∫ x : RealVector4, f (B⁻¹ • x) := by
      unfold poissonFourierIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [f, r, poissonTestFunction, smul_smul, mul_inv_cancel₀ hB.ne', one_smul]
    _ = (B : ℂ) ^ 4 * ∫ y : RealVector4, f y :=
      poisson_integral_comp_inv_smul f B hB.le
    _ = _ := by
      congr 1
      unfold deltaIntegral
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [f]
      have hphase : -inner ℝ v (B • y) = -inner ℝ ((r * B) • v) y / r := by
        rw [real_inner_smul_right, real_inner_smul_left]
        field_simp [hr]
      rw [hphase]

/-- The manuscript's frequency normalization uses Q=B/sqrt(q) exactly. -/
theorem poisson_frequency_scale (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 < B)
    (c : ℕ+) :
    (((c : ℝ) / (B / Real.sqrt (q : ℝ))) * B) *
      ((q * (c : ℕ) : ℕ) : ℝ)⁻¹ = (Real.sqrt (q : ℝ))⁻¹ := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr c.pos
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqR
  have hsq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hqR.le
  push_cast
  field_simp [hB.ne', hqR.ne', hcR.ne', hs.ne']
  nlinarith [hsq]

/-- The Fourier integral on the lattice qc has the exact B^4 delta-integral
normalization and frequency u/sqrt(q) from Lemma 5.1. -/
theorem poissonFourierIntegral_testFunction
    (A : Matrix (Fin 4) (Fin 4) ℤ) (q : ℕ) (B : ℝ) (w : RealVector4 → ℂ)
    (c : ℕ+) (u : Fin 4 → ℤ) (hq : 0 < q) (hB : 0 < B) :
    poissonFourierIntegral (poissonTestFunction A B (B / Real.sqrt (q : ℝ)) w c)
        (((q * (c : ℕ) : ℕ) : ℝ)⁻¹ • integerRealVector u) =
      (B : ℂ) ^ 4 * deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
        w ((c : ℝ) / (B / Real.sqrt (q : ℝ)))
        ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u) := by
  have hQ : 0 < B / Real.sqrt (q : ℝ) :=
    div_pos hB (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hq))
  rw [poissonFourierIntegral_testFunction_general A B (B / Real.sqrt (q : ℝ))
    w c _ hB hQ, smul_smul, poisson_frequency_scale q hq B hB c]

end QuaternaryQuadraticForms
