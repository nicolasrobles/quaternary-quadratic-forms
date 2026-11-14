import QuaternaryQuadraticForms.QuadraticTraceBound
import QuaternaryQuadraticForms.BadReductionResultants

/-!
# The full quadratic projective trace theorem

Characteristic-zero smoothness gives finiteness of the actual bad-prime
set by homogeneous elimination. The literal modulus then supplies both
odd nonsingular quadratic reduction and the geometric rank condition.
This closes the quadratic trace statement without a separate finiteness
or good-reduction premise.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The integer-valued version of Lemma 5.9. Finiteness of the literal
bad-prime set is proved from characteristic-zero smoothness inside the
definition of the modulus used in the hypothesis. -/
theorem quadratic_projective_trace_integer (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2)
    (hsmooth : SmoothCharacteristicZero A G)
    (hp : ¬ p ∣ polynomialBadPrimeModulus A G
      (badReductionPrimes_finite_of_smooth A (by decide : 2 ≤ 2) G hG hsmooth)) :
    (p : ℤ) ∣ integralProjectiveQuadraticTrace p A G ∧
      |integralProjectiveQuadraticTrace p A G| ≤ 4 * (p : ℤ) := by
  have hfinite := badReductionPrimes_finite_of_smooth A (by decide : 2 ≤ 2) G hG hsmooth
  obtain ⟨hpF, hgood⟩ :=
    (not_dvd_polynomialBadPrimeModulus_iff p A hdet G hfinite).mp hp
  exact ⟨integralProjectiveQuadraticTrace_dvd p (goodPrime_ne_two p A hpF) A hG,
    integralProjectiveQuadraticTrace_abs_le p A hA hpF hG hgood⟩

/-- Lemma 5.9 for the actual complex projective character sum: the sum is
an integer divisible by `p`, with absolute value at most `4p`. The only
geometric hypothesis is the manuscript's characteristic-zero rank
condition; neither finiteness nor good reduction is an extra premise. -/
theorem quadratic_projective_trace (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) ℤ} (hG : G.IsHomogeneous 2)
    (hsmooth : SmoothCharacteristicZero A G)
    (hp : ¬ p ∣ polynomialBadPrimeModulus A G
      (badReductionPrimes_finite_of_smooth A (by decide : 2 ≤ 2) G hG hsmooth)) :
    ∃ a : ℤ,
      projectiveTrace (reduceQuadraticMatrix p A) (complexQuadraticChar p)
        (G.map (Int.castRingHom (ZMod p))) = (a : ℂ) ∧
      (p : ℤ) ∣ a ∧ |a| ≤ 4 * (p : ℤ) := by
  have hfinite := badReductionPrimes_finite_of_smooth A (by decide : 2 ≤ 2) G hG hsmooth
  obtain ⟨hpF, hgood⟩ :=
    (not_dvd_polynomialBadPrimeModulus_iff p A hdet G hfinite).mp hp
  exact integralProjectiveTrace_quadratic_integral_dvd_bound p A hA hpF hG hgood

end QuaternaryQuadraticForms
