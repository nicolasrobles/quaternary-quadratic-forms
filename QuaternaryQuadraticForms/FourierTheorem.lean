import QuaternaryQuadraticForms.ExceptionalPlanePolynomial
import QuaternaryQuadraticForms.FourierBound

/-!
# The uniform polynomial Fourier bound

This is the full statement of Lemma 4.4 with the exceptional polynomial
supplied by Lemma 4.1(ii). The degree bound is chosen before the integral
polynomial and prime. For each admissible polynomial and good prime, the
same exceptional polynomial works for every allowed multiplicative character
and every integral frequency.
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The polynomial character weight, pointwise Fourier estimate, and zero
frequency identity of Lemma 4.4, with a uniformly bounded exceptional
polynomial chosen independently of the multiplicative character. -/
theorem uniform_polynomial_fourier_bound
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (G : MvPolynomial (Fin 4) ℤ) (hG : G.IsHomogeneous n)
        (hsmooth : SmoothCharacteristicZero A G)
        (p : ℕ) [Fact p.Prime],
        ¬ p ∣ polynomialBadPrimeModulus A G
          (badReductionPrimes_finite_of_smooth A hn G hG hsmooth) →
        ∃ D : MvPolynomial (Fin 4) (ZMod p),
          D ≠ 0 ∧ D.totalDegree ≤ E ∧ MvPolynomial.eval 0 D = 0 ∧
          (∀ u : Fin 4 → ZMod p, MvPolynomial.eval u D ≠ 0 →
            dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u) ≠ 0 ∧
            PlaneTransverseRank
              ((matrixQuadraticPolynomial (reduceQuadraticMatrix p A)).map
                (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
              ((G.map (Int.castRingHom (ZMod p))).map
                (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
              ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u)) ∧
          ∀ (ψ : MulChar (ZMod p) ℂ), ψ ≠ 1 → ψ ^ n = 1 →
            polynomialCharacterWeight ψ (G.map (Int.castRingHom (ZMod p)))
                (0 : Fin 4 → ZMod p) = 0 ∧
            (∀ x : Fin 4 → ZMod p,
              ‖polynomialCharacterWeight ψ (G.map (Int.castRingHom (ZMod p))) x‖ ≤ 1) ∧
            (∀ t : ZMod p, t ≠ 0 → ∀ x : Fin 4 → ZMod p,
              polynomialCharacterWeight ψ (G.map (Int.castRingHom (ZMod p))) (t • x) =
                polynomialCharacterWeight ψ (G.map (Int.castRingHom (ZMod p))) x) ∧
            (∀ u : Fin 4 → ℤ,
              ‖integralFourierSum p A ψ G u‖ ≤
                2 * (n : ℝ) ^ 2 *
                  ((p : ℝ) ^ (3 / 2 : ℝ) + (p : ℝ) ^ 2 *
                    (if MvPolynomial.eval (reduceFrequency p u) D = 0 then 1 else 0))) ∧
            integralFourierSum p A ψ G 0 =
              ((p : ℂ) - 1) * projectiveTrace (reduceQuadraticMatrix p A) ψ
                (G.map (Int.castRingHom (ZMod p))) := by
  obtain ⟨E, hE, hpoly⟩ := exceptional_plane_polynomial A hA hdet n hn
  refine ⟨E, hE, ?_⟩
  intro G hG hsmooth p _ hp
  obtain ⟨D, hD, hdegree, hzero, hplanes⟩ := hpoly G hG hsmooth p hp
  refine ⟨D, hD, hdegree, hzero, hplanes, ?_⟩
  intro ψ hψ horder
  exact fourier_bound p A hA hdet hG hn hsmooth hp D hzero hplanes ψ hψ horder

end QuaternaryQuadraticForms
