import QuaternaryQuadraticForms.SourceAverageFrequencyTheorem

/-! # The uniform arithmetic data in the Section 5 estimates -/

namespace QuaternaryQuadraticForms

/-- The excluded primes, local weights, exceptional polynomials, and bounds
from Section 3. The degree bound and Fourier constant precede the data. -/
structure FrequencySourceData (A : Matrix (Fin 4) (Fin 4) ℤ) (E K : ℝ) where
  N : ℕ
  N_pos : 1 ≤ N
  radical_dvd : primeRadical (quadraticBadPrimeModulus A) ∣ N
  D : ∀ p : ℕ, p.Prime → ¬p ∣ N → MvPolynomial (Fin 4) (ZMod p)
  poly_nonzero : ∀ p hp hN, D p hp hN ≠ 0
  degree_le : ∀ p hp hN, ((D p hp hN).totalDegree : ℝ) ≤ E
  ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ
  zero_value : ∀ p hp hN, ξ p hp hN 0 = 0
  invariant : ∀ p hp hN, ∀ r : ZMod p, r ≠ 0 → ∀ y, ξ p hp hN (r • y) = ξ p hp hN y
  norm_le : ∀ p hp hN x, ‖ξ p hp hN x‖ ≤ 1
  fourier_bound : ∀ p (hp : p.Prime) (hN : ¬p ∣ N) (u : Fin 4 → ℤ),
    ‖@sourceConstrainedFourierSum N ξ p ⟨hp.ne_zero⟩
      (hp.coprime_iff_not_dvd.mpr hN) A u‖ ≤
      K * ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ)^2 *
        (if MvPolynomial.eval (fun i => (u i : ZMod p)) (D p hp hN) = 0 then 1 else 0))

end QuaternaryQuadraticForms
