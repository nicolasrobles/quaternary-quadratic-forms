import QuaternaryQuadraticForms.PoissonDefinitions

/-!
# Registered classical four-dimensional Poisson input

The source is the general affine-lattice Poisson formula used in Heath--Brown,
Section 3, proof of Theorem 2 (author manuscript pp.19--20), with the standard
absolute-convergence clause for smooth compact support. The exact statement
was preregistered under EXT.POISSON_R4. No manuscript-specific function,
complete sum, or delta-Poisson identity is imported.
See certification/correspondence/poisson_summation.md.
-/

noncomputable section

open scoped BigOperators

axiom QuaternaryQuadraticForms.Trusted.poisson_four_dimensional :
  ∀ (g : QuaternaryQuadraticForms.RealVector4 → ℂ) (L : ℝ),
    QuaternaryQuadraticForms.IsSmoothWeight g → 0 < L →
    Summable (fun u : Fin 4 → ℤ =>
      ‖QuaternaryQuadraticForms.poissonFourierIntegral g
        (L⁻¹ • QuaternaryQuadraticForms.integerRealVector u)‖) ∧
    ∀ z : QuaternaryQuadraticForms.RealVector4,
      (∑' x : Fin 4 → ℤ,
        g (z + L • QuaternaryQuadraticForms.integerRealVector x)) =
      ((L : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((inner ℝ (L⁻¹ • QuaternaryQuadraticForms.integerRealVector u) z : ℝ) : ℂ)) *
        QuaternaryQuadraticForms.poissonFourierIntegral g
          (L⁻¹ • QuaternaryQuadraticForms.integerRealVector u)
