import QuaternaryQuadraticForms.FourierOrthogonality
import QuaternaryQuadraticForms.PrimeQuadraticGauss
import QuaternaryQuadraticForms.DiagonalPencil

/-!
# The exact Gauss expansion of the diagonal Fourier sum

Both character orthogonality identities are applied to the actual cone
Fourier sum. The nonzero Gauss parameter permits the substitution `v=s t`.
The resulting identity keeps every pencil parameter, including all four
singular members.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Gauss inversion with the additional Fourier phase. -/
theorem primeQuadraticGauss_phase_expansion (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (m c : ZMod p) :
    primeQuadraticGauss p * complexQuadraticChar p m * ZMod.stdAddChar c =
      ∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
        ZMod.stdAddChar ((s : ZMod p) * m + c) := by
  calc
    _ = (complexQuadraticChar p m * primeQuadraticGauss p) * ZMod.stdAddChar c := by
      ring
    _ = (∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
          ZMod.stdAddChar ((s : ZMod p) * m)) * ZMod.stdAddChar c := by
      rw [primeQuadraticGauss_units_inversion p hp]
    _ = _ := by
      simp only [Finset.sum_mul, AddChar.map_add_eq_mul, mul_assoc]

/-- The actual cone Fourier sum after additive orthogonality and quadratic
Gauss inversion. The zero Gauss parameter has already been removed. -/
theorem fourierSum_quadraticGauss_expansion (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (G : MvPolynomial (Fin 4) (ZMod p)) (u : PrimeVector p) :
    (p : ℂ) * primeQuadraticGauss p * fourierSum A (complexQuadraticChar p) G u =
      ∑ s : (ZMod p)ˣ, complexQuadraticChar p (s : ZMod p) *
        ∑ v : ZMod p, ∑ x : PrimeVector p,
          ZMod.stdAddChar ((s : ZMod p) * MvPolynomial.eval x G +
            v * quadraticValue A x + dotProduct u x) := by
  classical
  calc
    _ = primeQuadraticGauss p *
        ((p : ℂ) * fourierSum A (complexQuadraticChar p) G u) := by ring
    _ = primeQuadraticGauss p *
        ∑ v : ZMod p, ∑ x : PrimeVector p,
          polynomialCharacterWeight (complexQuadraticChar p) G x *
            ZMod.stdAddChar (v * quadraticValue A x + dotProduct u x) := by
      rw [fourierSum_additive_expansion]
    _ = ∑ v : ZMod p, ∑ x : PrimeVector p, ∑ s : (ZMod p)ˣ,
        complexQuadraticChar p (s : ZMod p) *
          ZMod.stdAddChar ((s : ZMod p) * MvPolynomial.eval x G +
            v * quadraticValue A x + dotProduct u x) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro x _
      simpa only [polynomialCharacterWeight, mul_assoc, add_assoc] using
        primeQuadraticGauss_phase_expansion p hp (MvPolynomial.eval x G)
          (v * quadraticValue A x + dotProduct u x)
    _ = ∑ v : ZMod p, ∑ s : (ZMod p)ˣ, ∑ x : PrimeVector p,
        complexQuadraticChar p (s : ZMod p) *
          ZMod.stdAddChar ((s : ZMod p) * MvPolynomial.eval x G +
            v * quadraticValue A x + dotProduct u x) := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.sum_comm
    _ = ∑ s : (ZMod p)ˣ, ∑ v : ZMod p, ∑ x : PrimeVector p,
        complexQuadraticChar p (s : ZMod p) *
          ZMod.stdAddChar ((s : ZMod p) * MvPolynomial.eval x G +
            v * quadraticValue A x + dotProduct u x) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

/-- The source pencil expansion, with the exact four one-dimensional
quadratic factors and every value of the pencil parameter retained. -/
theorem diagonal_fourier_pencil_expansion (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (a b u : Fin 4 → ZMod p) :
    (p : ℂ) * primeQuadraticGauss p *
        fourierSum (Matrix.diagonal a) (complexQuadraticChar p)
          (matrixQuadraticPolynomial (Matrix.diagonal b)) u =
      ∑ t : ZMod p, ∑ s : (ZMod p)ˣ,
        complexQuadraticChar p (s : ZMod p) *
          ∏ i : Fin 4, primeQuadraticExponentialSum p
            ((s : ZMod p) * diagonalPencilCoeff a b t i) (u i) := by
  classical
  rw [fourierSum_quadraticGauss_expansion p hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ t : ZMod p, ∑ x : PrimeVector p,
        ZMod.stdAddChar ((s : ZMod p) *
          MvPolynomial.eval x (matrixQuadraticPolynomial (Matrix.diagonal b)) +
          ((s : ZMod p) * t) * quadraticValue (Matrix.diagonal a) x + dotProduct u x) := by
      exact (Fintype.sum_bijective (fun t : ZMod p => (s : ZMod p) * t)
        s.mulLeft_bijective _ _ (fun _ => rfl)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simpa only [primeQuadraticExponentialSum, diagonalPencilCoeff] using
        diagonal_exponential_sum_factorization p a b u (s : ZMod p) t

end QuaternaryQuadraticForms
