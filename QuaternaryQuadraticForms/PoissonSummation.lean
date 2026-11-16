import QuaternaryQuadraticForms.Trusted.Poisson
import QuaternaryQuadraticForms.CRTCharacters

/-!
# Specializing classical Poisson summation to the actual integer lattice

The general registered real affine-lattice formula is converted to the
manuscript's standard additive character. The inner-product and character
identities, including all signs and casts, are proved internally.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The Euclidean inner product of integer vectors is the real cast of
their literal integral dot product. -/
theorem integerRealVector_inner (u z : Fin 4 → ℤ) :
    inner ℝ (integerRealVector u) (integerRealVector z) =
      ((dotProduct u z : ℤ) : ℝ) := by
  simp [integerRealVector, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_comm]

/-- The positive affine-lattice Fourier phase is the standard additive
character modulo the integer lattice spacing. -/
theorem poisson_affine_phase_eq_stdAddChar (m : ℕ) [NeZero m]
    (u z : Fin 4 → ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((inner ℝ ((m : ℝ)⁻¹ • integerRealVector u) (integerRealVector z) : ℝ) : ℂ)) =
        ZMod.stdAddChar ((dotProduct u z : ℤ) : ZMod m) := by
  rw [real_inner_smul_left, integerRealVector_inner, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- Classical four-dimensional Poisson summation on the exact affine
integer lattice, with the source standard-character normalization. -/
theorem poisson_affine_integer_lattice (g : RealVector4 → ℂ)
    (hg : IsSmoothWeight g) (m : ℕ) [NeZero m] :
    Summable (fun u : Fin 4 → ℤ =>
      ‖poissonFourierIntegral g ((m : ℝ)⁻¹ • integerRealVector u)‖) ∧
    ∀ z : Fin 4 → ℤ,
      (∑' x : Fin 4 → ℤ,
        g (integerRealVector z + (m : ℝ) • integerRealVector x)) =
        ((m : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
          ZMod.stdAddChar ((dotProduct u z : ℤ) : ZMod m) *
            poissonFourierIntegral g ((m : ℝ)⁻¹ • integerRealVector u) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  obtain ⟨hsum, hformula⟩ := Trusted.poisson_four_dimensional g (m : ℝ) hg hm
  refine ⟨hsum, ?_⟩
  intro z
  simpa only [Complex.ofReal_natCast, poisson_affine_phase_eq_stdAddChar] using
    hformula (integerRealVector z)

end QuaternaryQuadraticForms
