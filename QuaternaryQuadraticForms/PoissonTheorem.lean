import QuaternaryQuadraticForms.PoissonFormula
import QuaternaryQuadraticForms.PoissonDeltaInsertion
import QuaternaryQuadraticForms.PoissonNormalization

/-!
# Lemma 5.1: the complete source delta-Poisson identity

The source weight family is retained in both the lattice sum and the complete
sums. The theorem includes actual finite support in the lattice and modulus
variables and absolute convergence at every positive modulus.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The manuscript's mixed complete sum, using only its supplied good-prime functions. -/
def sourceMixedCompleteSum (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N) (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) : ℂ :=
  ∑ a : (ZMod c)ˣ, ∑ z : Fin 4 → ZMod (q * c),
    if (q : ℤ) ∣ integralQuadraticValue A (residueLift (q * c) z) then
      sourceCompositeWeight N ξ q hqN (residueLift (q * c) z) *
        ZMod.stdAddChar
          ((((a : ZMod c).val : ℤ) * integralQuadraticValue A (residueLift (q * c) z) +
            dotProduct u (residueLift (q * c) z) : ℤ) : ZMod (q * c))
    else 0

/-- The total-family representation gives exactly the original source mixed sum. -/
theorem mixedCompleteSum_extend_eq_source (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N) (c : ℕ) [NeZero c]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (u : Fin 4 → ℤ) :
    mixedCompleteSum (extendPrimeWeights N ξ) q c A u =
      sourceMixedCompleteSum N ξ q hqN c A u := by
  simp only [mixedCompleteSum, mixedIntegerSummand, sourceMixedCompleteSum,
    compositeWeight_extend_eq_source N q ξ hqN]

/-- The exact delta-Poisson identity with the literal total-family representation. -/
theorem weightedQuadraticZeroSum_poisson
    (ξ : ∀ p : ℕ, (Fin 4 → ZMod p) → ℂ) (q : ℕ) [NeZero q]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (hQ : 3 ≤ B / Real.sqrt (q : ℝ)) (w : RealVector4 → ℂ)
    (hw : IsSmoothWeight w) :
    weightedQuadraticZeroSum ξ q A B w =
      ((heathBrownNormalization (B / Real.sqrt (q : ℝ)) * B ^ 2 / (q : ℝ) ^ 3 : ℝ) : ℂ) *
        ∑' c : ℕ+, poissonModulusTerm ξ q A B w c := by
  calc
    _ = ((heathBrownNormalization (B / Real.sqrt (q : ℝ)) /
        (B / Real.sqrt (q : ℝ)) ^ 2 : ℝ) : ℂ) *
        ∑' c : ℕ+, ((B : ℂ) ^ 4 / (q : ℂ) ^ 4) * poissonModulusTerm ξ q A B w c := by
      rw [weightedQuadraticZeroSum_delta ξ q A B hB hQ w hw.2]
      congr 1
      exact tsum_congr (fun c => (poisson_test_function_complete_sum ξ q A B hB w hw c).1)
    _ = _ := by
      rw [tsum_mul_left, ← mul_assoc,
        poisson_normalization_factor q B hB (heathBrownNormalization (B / Real.sqrt (q : ℝ)))]

/-- Complete Lemma 5.1 for the original source functions. Besides the exact
identity, the literal lattice sum has finite support, only finitely many
positive moduli contribute, and every frequency series converges absolutely.
The proof applies to every positive q, so in particular to the source's
squarefree moduli, without a Fourier bound or annular-support assumption. -/
theorem source_delta_poisson (N : ℕ)
    (ξ : ∀ p : ℕ, p.Prime → ¬p ∣ N → (Fin 4 → ZMod p) → ℂ)
    (q : ℕ) [NeZero q] (hqN : q.Coprime N)
    (A : Matrix (Fin 4) (Fin 4) ℤ) (B : ℝ) (hB : 0 < B)
    (hQ : 3 ≤ B / Real.sqrt (q : ℝ)) (w : RealVector4 → ℂ)
    (hw : IsSmoothWeight w) :
    (Function.support (fun x : Fin 4 → ℤ => if integralQuadraticValue A x = 0 then
      w (B⁻¹ • integerRealVector x) * sourceCompositeWeight N ξ q hqN x else 0)).Finite ∧
    (sourceQuadraticZeroSum N ξ q hqN A B w =
      ((heathBrownNormalization (B / Real.sqrt (q : ℝ)) * B ^ 2 / (q : ℝ) ^ 3 : ℝ) : ℂ) *
        ∑' c : ℕ+, ((c : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
          sourceMixedCompleteSum N ξ q hqN (c : ℕ) A u *
            deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
              w ((c : ℝ) / (B / Real.sqrt (q : ℝ)))
              ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u)) ∧
    (Function.support (fun c : ℕ+ => ((c : ℂ) ^ 4)⁻¹ * ∑' u : Fin 4 → ℤ,
      sourceMixedCompleteSum N ξ q hqN (c : ℕ) A u *
        deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
          w ((c : ℝ) / (B / Real.sqrt (q : ℝ)))
          ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u))).Finite ∧
    ∀ c : ℕ+, Summable (fun u : Fin 4 → ℤ =>
      ‖sourceMixedCompleteSum N ξ q hqN (c : ℕ) A u *
        deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ)))
          w ((c : ℝ) / (B / Real.sqrt (q : ℝ)))
          ((Real.sqrt (q : ℝ))⁻¹ • integerRealVector u)‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [compositeWeight_extend_eq_source N q ξ hqN] using
      weightedQuadraticZeroSum_finite_support (extendPrimeWeights N ξ) q A B hB w hw.2
  · simpa only [weightedQuadraticZeroSum_extend_eq_source N q ξ hqN,
      poissonModulusTerm, poissonFrequencyTerm, mixedCompleteSum_extend_eq_source N ξ q hqN] using
      weightedQuadraticZeroSum_poisson (extendPrimeWeights N ξ) q A B hB hQ w hw
  · have hfinite := poissonModulusTerm_finite_support (extendPrimeWeights N ξ) q A B hB w hw.2
    change (Function.support (fun c : ℕ+ =>
      poissonModulusTerm (extendPrimeWeights N ξ) q A B w c)).Finite at hfinite
    simpa only [poissonModulusTerm, poissonFrequencyTerm,
      mixedCompleteSum_extend_eq_source N ξ q hqN] using hfinite
  · intro c
    simpa only [poissonFrequencyTerm, mixedCompleteSum_extend_eq_source N ξ q hqN] using
      (poisson_test_function_complete_sum (extendPrimeWeights N ξ) q A B hB w hw c).2

end QuaternaryQuadraticForms
