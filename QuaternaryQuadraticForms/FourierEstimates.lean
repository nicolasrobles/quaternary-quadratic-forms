import QuaternaryQuadraticForms.KatzBound
import QuaternaryQuadraticForms.PlaneSectionTheorem
import QuaternaryQuadraticForms.FourierBoundConstants
import QuaternaryQuadraticForms.PlaneSectionCardinality

/-!
# Estimates for the actual Fourier sum

The ray identity reduces the norm of the literal Fourier sum to the global
projective trace and its actual plane section. The generic, exceptional and
zero-frequency estimates retain the manuscript's exact constants.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The triangle inequality applied to the literal ray identity. -/
theorem fourierSum_norm_le_section_and_trace (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (ψ : MulChar (ZMod p) ℂ)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (horder : ψ ^ n = 1)
    (u : Fin 4 → ZMod p) :
    ‖fourierSum A ψ G u‖ ≤
      (p : ℝ) * ‖projectiveSectionTrace A ψ G u‖ + ‖projectiveTrace A ψ G‖ := by
  rw [fourierSum_ray_identity A ψ hG hn horder]
  simpa only [norm_mul, Complex.norm_natCast] using
    norm_sub_le ((p : ℂ) * projectiveSectionTrace A ψ G u) (projectiveTrace A ψ G)

/-- The exact norm of the zero-frequency sum, including the real factor `p-1`. -/
theorem fourierSum_zero_norm (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (ψ : MulChar (ZMod p) ℂ)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 0 < n) (horder : ψ ^ n = 1) :
    ‖fourierSum A ψ G 0‖ = ((p : ℝ) - 1) * ‖projectiveTrace A ψ G‖ := by
  have hp : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hnorm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one] using
      (Complex.norm_of_nonneg (r := (p : ℝ) - 1) (sub_nonneg.mpr hp))
  rw [fourierSum_zero A ψ hG hn horder, norm_mul, hnorm]

/-- The generic-frequency estimate from the actual Katz and transverse
plane-section bounds, with the manuscript's constant `2 n²`. -/
theorem fourierSum_generic_bound (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (u : Fin 4 → ZMod p) (hu : dotProduct u (A.adjugate.mulVec u) ≠ 0)
    (hplane : PlaneTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u)) :
    ‖fourierSum A ψ G u‖ ≤ 2 * (n : ℝ) ^ 2 * (p : ℝ) * Real.sqrt p := by
  have hpR : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hglobal := katz_quadric_bound_prime_field p hp A hA hdet ψ hψ
    hG hn horder htrans
  have hsection := plane_section_bound_prime_field p hp A hA hdet u hu ψ hψ
    hG hn horder hplane
  calc
    ‖fourierSum A ψ G u‖ ≤
        (p : ℝ) * ‖projectiveSectionTrace A ψ G u‖ + ‖projectiveTrace A ψ G‖ :=
      fourierSum_norm_le_section_and_trace p A ψ hG (by omega) horder u
    _ ≤ (p : ℝ) * ((2 * (n : ℝ) - 1) * Real.sqrt p + 1) +
        (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hsection (Nat.cast_nonneg p)) hglobal
    _ = (2 * (n : ℝ) - 1) * (p : ℝ) * Real.sqrt p +
        (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 5) * (p : ℝ) := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (p : ℝ) * Real.sqrt p :=
      fourier_generic_constant_bound n hn p hpR

/-- The zero-frequency estimate, deduced from the exact identity and
the actual projective Katz bound. -/
theorem fourierSum_zero_bound (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) :
    ‖fourierSum A ψ G 0‖ ≤ 2 * (n : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  have hpR : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hglobal := katz_quadric_bound_prime_field p hp A hA hdet ψ hψ
    hG hn horder htrans
  rw [fourierSum_zero_norm p A ψ hG (by omega) horder]
  calc
    ((p : ℝ) - 1) * ‖projectiveTrace A ψ G‖ ≤
        ((p : ℝ) - 1) * ((2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hglobal (sub_nonneg.mpr hpR)
    _ = ((p : ℝ) - 1) * (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ) := by
      ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (p : ℝ) ^ 2 :=
      fourier_zero_constant_bound n hn p hpR

/-- Every nonzero frequency has the exceptional `p²` bound, including
frequencies whose actual plane section is tangent or singular. -/
theorem fourierSum_nonzero_bound (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (u : Fin 4 → ZMod p) (hu : u ≠ 0) :
    ‖fourierSum A ψ G u‖ ≤ 2 * (n : ℝ) ^ 2 * (p : ℝ) ^ 2 := by
  have hpR : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hglobal := katz_quadric_bound_prime_field p hp A hA hdet ψ hψ
    hG hn horder htrans
  have hsection := projectiveSectionTrace_norm_le p hp A hA hdet u hu ψ G
  calc
    ‖fourierSum A ψ G u‖ ≤
        (p : ℝ) * ‖projectiveSectionTrace A ψ G u‖ + ‖projectiveTrace A ψ G‖ :=
      fourierSum_norm_le_section_and_trace p A ψ hG (by omega) horder u
    _ ≤ (p : ℝ) * (2 * (p : ℝ) + 2) +
        (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 4) * (p : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hsection (Nat.cast_nonneg p)) hglobal
    _ = 2 * (p : ℝ) ^ 2 + (2 * (n : ℝ) ^ 2 - 4 * (n : ℝ) + 6) * (p : ℝ) := by
      ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (p : ℝ) ^ 2 :=
      fourier_exceptional_constant_bound n hn p hpR

end QuaternaryQuadraticForms
