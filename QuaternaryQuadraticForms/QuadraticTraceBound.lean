import QuaternaryQuadraticForms.KatzBound
import QuaternaryQuadraticForms.QuadraticTrace

/-!
# The size of the quadratic projective trace

The degree-two Katz specialization bounds the actual integer trace by `4p`.
It is combined with the previously proved integrality and divisibility.
The final wrappers use the literal good-reduction modulus; their explicit
finiteness argument must be supplied by the separate elimination deduction.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The degree-two Katz bound for the actual integer-valued projective trace. -/
theorem projectiveQuadraticTrace_abs_le (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) (ZMod p)} (hG : G.IsHomogeneous 2)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) :
    |projectiveQuadraticTrace A G| ≤ 4 * (p : ℤ) := by
  have hbound := katz_quadric_bound_prime_field p hp A hA hdet
    (complexQuadraticChar p) (complexQuadraticChar_ne_one p hp) hG (by decide)
    (complexQuadraticChar_sq p) htrans
  rw [← projectiveQuadraticTrace_complex, Complex.norm_intCast] at hbound
  norm_num at hbound
  exact_mod_cast hbound

/-- Integrality, divisibility, and the size bound for the actual complex
quadratic trace over the prime field. -/
theorem projectiveTrace_quadratic_integral_dvd_bound (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) (ZMod p)} (hG : G.IsHomogeneous 2)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) :
    ∃ a : ℤ, projectiveTrace A (complexQuadraticChar p) G = (a : ℂ) ∧
      (p : ℤ) ∣ a ∧ |a| ≤ 4 * (p : ℤ) :=
  ⟨projectiveQuadraticTrace A G, (projectiveQuadraticTrace_complex A G).symm,
    projectiveQuadraticTrace_dvd hp A hG,
    projectiveQuadraticTrace_abs_le p hp A hA hdet hG htrans⟩

/-- The integer trace bound for integral coefficients and the actual
geometric good-reduction condition. -/
theorem integralProjectiveQuadraticTrace_abs_le (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2)
    (hgood : GoodReductionAt p A G) :
    |integralProjectiveQuadraticTrace p A G| ≤ 4 * (p : ℤ) :=
  projectiveQuadraticTrace_abs_le p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp) (homogeneous_reduce_mod hG p) hgood

/-- The three quadratic-trace conclusions with integral input coefficients
and explicit good reduction, tied to the existing complex trace. -/
theorem integralProjectiveTrace_quadratic_integral_dvd_bound (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A)
    (hp : ¬ p ∣ quadraticBadPrimeModulus A)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2)
    (hgood : GoodReductionAt p A G) :
    ∃ a : ℤ,
      projectiveTrace (reduceQuadraticMatrix p A) (complexQuadraticChar p)
        (G.map (Int.castRingHom (ZMod p))) = (a : ℂ) ∧
      (p : ℤ) ∣ a ∧ |a| ≤ 4 * (p : ℤ) :=
  projectiveTrace_quadratic_integral_dvd_bound p (goodPrime_ne_two p A hp)
    (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
    (goodPrime_reduced_det_ne_zero p A hp) (homogeneous_reduce_mod hG p) hgood

/-- The literal `N_G` condition gives divisibility and the size bound for
the actual integer trace once the finite bad-prime set has been proved. -/
theorem integralProjectiveQuadraticTrace_dvd_bound_of_modulus (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2)
    (hfinite : (badReductionPrimes A G).Finite)
    (hp : ¬ p ∣ polynomialBadPrimeModulus A G hfinite) :
    (p : ℤ) ∣ integralProjectiveQuadraticTrace p A G ∧
      |integralProjectiveQuadraticTrace p A G| ≤ 4 * (p : ℤ) := by
  obtain ⟨hpF, hgood⟩ :=
    (not_dvd_polynomialBadPrimeModulus_iff p A hdet G hfinite).mp hp
  exact ⟨integralProjectiveQuadraticTrace_dvd p (goodPrime_ne_two p A hpF) A hG,
    integralProjectiveQuadraticTrace_abs_le p A hA hpF hG hgood⟩

/-- The source-level quadratic trace conclusions under the literal `N_G`
condition, with the still-required finiteness deduction explicit. -/
theorem integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus
    (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2)
    (hfinite : (badReductionPrimes A G).Finite)
    (hp : ¬ p ∣ polynomialBadPrimeModulus A G hfinite) :
    ∃ a : ℤ,
      projectiveTrace (reduceQuadraticMatrix p A) (complexQuadraticChar p)
        (G.map (Int.castRingHom (ZMod p))) = (a : ℂ) ∧
      (p : ℤ) ∣ a ∧ |a| ≤ 4 * (p : ℤ) := by
  obtain ⟨hpF, hgood⟩ :=
    (not_dvd_polynomialBadPrimeModulus_iff p A hdet G hfinite).mp hp
  exact integralProjectiveTrace_quadratic_integral_dvd_bound p A hA hpF hG hgood

end QuaternaryQuadraticForms
