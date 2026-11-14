import QuaternaryQuadraticForms.FourierEstimates
import QuaternaryQuadraticForms.ExceptionalPlanePolynomial

/-!
# The polynomial Fourier estimate

The three frequency cases give the pointwise bound for the actual Fourier
sum. The integral theorem obtains odd characteristic, nonsingular quadratic
reduction and geometric transversality from the literal modulus `N_G`.
Its exceptional polynomial is the same one supplied by Lemma 4.1(ii).
-/

noncomputable section

namespace QuaternaryQuadraticForms

/-- The actual finite-field Fourier bound for any exceptional polynomial
with the geometric properties supplied by Lemma 4.1(ii). -/
theorem fourierSum_bound_prime_field (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    {G : MvPolynomial (Fin 4) (ZMod p)} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n) (horder : ψ ^ n = 1)
    (htrans : ProjectiveIntersectionTransverseRank
      ((matrixQuadraticPolynomial A).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
      (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (D : MvPolynomial (Fin 4) (ZMod p)) (hDzero : MvPolynomial.eval 0 D = 0)
    (hDplanes : ∀ u : Fin 4 → ZMod p, MvPolynomial.eval u D ≠ 0 →
      dotProduct u (A.adjugate.mulVec u) ≠ 0 ∧
      PlaneTransverseRank
        ((matrixQuadraticPolynomial A).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
        (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
        ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u))
    (u : Fin 4 → ZMod p) :
    ‖fourierSum A ψ G u‖ ≤
      2 * (n : ℝ) ^ 2 * ((p : ℝ) ^ (3 / 2 : ℝ) +
        (p : ℝ) ^ 2 * (if MvPolynomial.eval u D = 0 then 1 else 0)) := by
  classical
  rw [rpow_three_halves_eq_mul_sqrt p (Nat.cast_nonneg p)]
  have hallow : 2 * (n : ℝ) ^ 2 * (p : ℝ) ^ 2 ≤
      2 * (n : ℝ) ^ 2 * ((p : ℝ) * Real.sqrt p + (p : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg p) (Real.sqrt_nonneg p)))
      (by positivity)
  by_cases hu : u = 0
  · subst u
    simp only [hDzero, ite_true, mul_one]
    exact (fourierSum_zero_bound p hp A hA hdet ψ hψ hG hn horder htrans).trans hallow
  by_cases hD : MvPolynomial.eval u D = 0
  · simp only [hD, ite_true, mul_one]
    exact (fourierSum_nonzero_bound p hp A hA hdet ψ hψ hG hn horder htrans u hu).trans
      hallow
  · simp only [hD, ite_false, mul_zero, add_zero]
    obtain ⟨hdual, hplane⟩ := hDplanes u hD
    simpa only [mul_assoc] using
      fourierSum_generic_bound p hp A hA hdet ψ hψ hG hn horder htrans u hdual hplane

/-- All clauses of Lemma 4.4 for the manuscript's integral data and literal
good-prime modulus, using any exceptional polynomial from Lemma 4.1(ii). -/
theorem fourier_bound
    (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℤ) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    {G : MvPolynomial (Fin 4) ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (hn : 2 ≤ n)
    (hsmooth : SmoothCharacteristicZero A G)
    (hp : ¬ p ∣ polynomialBadPrimeModulus A G
      (badReductionPrimes_finite_of_smooth A hn G hG hsmooth))
    (D : MvPolynomial (Fin 4) (ZMod p)) (hDzero : MvPolynomial.eval 0 D = 0)
    (hDplanes : ∀ u : Fin 4 → ZMod p, MvPolynomial.eval u D ≠ 0 →
      dotProduct u ((reduceQuadraticMatrix p A).adjugate.mulVec u) ≠ 0 ∧
      PlaneTransverseRank
        ((matrixQuadraticPolynomial (reduceQuadraticMatrix p A)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
        ((G.map (Int.castRingHom (ZMod p))).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))
        ((algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∘ u))
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1) (horder : ψ ^ n = 1) :
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
  have hfinite := badReductionPrimes_finite_of_smooth A hn G hG hsmooth
  obtain ⟨hpF, hgood⟩ :=
    (not_dvd_polynomialBadPrimeModulus_iff p A hdet G hfinite).mp hp
  obtain ⟨hzero, hnorm, hscalar⟩ := polynomialCharacterWeight_properties ψ
    (hG.map (Int.castRingHom (ZMod p))) (by omega) horder
  refine ⟨hzero, hnorm, hscalar, ?_, ?_⟩
  · intro u
    exact fourierSum_bound_prime_field p (goodPrime_ne_two p A hpF)
      (reduceQuadraticMatrix p A) (reduceQuadraticMatrix_symmetric p A hA)
      (goodPrime_reduced_det_ne_zero p A hpF) ψ hψ
      (hG.map (Int.castRingHom (ZMod p))) hn horder hgood D hDzero hDplanes
      (reduceFrequency p u)
  · exact integralFourierSum_of_dvd p A ψ hG (by omega) horder 0 (by intro i; simp)

end QuaternaryQuadraticForms
