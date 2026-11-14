import QuaternaryQuadraticForms.DiagonalPencilFormula
import QuaternaryQuadraticForms.DiagonalPencilCubic
import QuaternaryQuadraticForms.CubicCharacterSum
import QuaternaryQuadraticForms.QuadraticTrace
import QuaternaryQuadraticForms.FourierBoundConstants

/-!
# Trace and generic bound from the diagonal pencil

The exact pencil formula gives the projective trace at zero frequency.
At a frequency with four nonzero coordinates and nonzero dual value, only
the cubic character sum remains. Its four deleted parameters contribute
the explicit `4p` term in the source estimate.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The diagonal projective trace is the sum of the four singular-pencil
characters, multiplied by the prime. -/
theorem diagonal_projectiveTrace_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0) :
    projectiveTrace (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) =
      (p : ℂ) * ∑ i : Fin 4, complexQuadraticChar p (diagonalKappa a b i) := by
  classical
  have hformula := diagonal_fourier_pencil_formula p hp a b 0 ha hpair
  have hphi : diagonalPencilPhi a b (0 : Fin 4 → ZMod p) = 0 := by
    simp [diagonalPencilPhi]
  have hnu (i : Fin 4) : diagonalPencilNu a b (0 : Fin 4 → ZMod p) i = 0 := by
    simp [diagonalPencilNu]
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (Fact.out : p.Prime).ne_one
  apply mul_left_cancel₀ hp1
  calc
    ((p : ℂ) - 1) * projectiveTrace (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) =
        fourierSum (Matrix.diagonal a) (complexQuadraticChar p)
          (matrixQuadraticPolynomial (Matrix.diagonal b)) 0 :=
      (fourierSum_zero (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial_homogeneous (Matrix.diagonal b)) (by decide)
        (complexQuadraticChar_sq p)).symm
    _ = (p : ℂ) * ∑ i : Fin 4,
        complexQuadraticChar p (diagonalKappa a b i) * ((p : ℂ) - 1) := by
      simpa [hphi, hnu, primeRamanujan_eq] using hformula
    _ = ((p : ℂ) - 1) *
        ((p : ℂ) * ∑ i : Fin 4, complexQuadraticChar p (diagonalKappa a b i)) := by
      rw [← Finset.sum_mul]
      ring

/-- The same identity holds for the literal integer-valued projective trace. -/
theorem diagonal_projectiveQuadraticTrace_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0) :
    projectiveQuadraticTrace (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) =
      (p : ℤ) * ∑ i : Fin 4, quadraticChar (ZMod p) (diagonalKappa a b i) := by
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [projectiveQuadraticTrace_complex]
  simpa only [complexQuadraticChar_apply] using
    diagonal_projectiveTrace_eq p hp a b ha hpair

/-- Nonzero coordinate frequencies remove all singular members; the remaining
cubic sum gives the explicit square-root bound. -/
theorem diagonal_fourier_generic_bound_sqrt (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b u : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0)
    (hu : ∀ i, u i ≠ 0)
    (hdual : MvPolynomial.eval u
      (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate) ≠ 0) :
    ‖fourierSum (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u‖ ≤
      2 * (p : ℝ) * Real.sqrt p + 4 * (p : ℝ) := by
  classical
  have hdegree : (-diagonalPencilPhi a b u).natDegree = 3 := by
    rw [Polynomial.natDegree_neg]
    apply diagonalPencilPhi_natDegree_eq_three a b u
    simpa only [eval_matrixQuadraticPolynomial] using hdual
  have hcubic := quadraticChar_cubic_sum_sdiff_four_norm_le p
    (five_le_of_diagonalPencil_roots p a b ha hpair)
    (-diagonalPencilPhi a b u) hdegree (diagonalPencilRoots a b)
    (diagonalPencilRoots_card_le a b)
  have hfilter : (Finset.univ.filter (fun i : Fin 4 => u i = 0)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact hu i
  rw [diagonal_fourier_pencil_formula p hp a b u ha hpair, hfilter,
    Finset.sum_empty, mul_zero, add_zero, norm_mul, Complex.norm_natCast]
  calc
    (p : ℝ) * ‖∑ t ∈ Finset.univ \ diagonalPencilRoots a b,
        complexQuadraticChar p (-(diagonalPencilPhi a b u).eval t)‖ ≤
        (p : ℝ) * (2 * Real.sqrt p + 4) :=
      mul_le_mul_of_nonneg_left (by simpa only [Polynomial.eval_neg] using hcubic)
        (Nat.cast_nonneg p)
    _ = 2 * (p : ℝ) * Real.sqrt p + 4 * (p : ℝ) := by ring

/-- The generic-frequency conclusion in the source's real `3/2` exponent
notation, for the actual diagonal Fourier sum. -/
theorem diagonal_fourier_generic_bound (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b u : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0)
    (hpair : ∀ i j : Fin 4, i ≠ j → a i * b j - a j * b i ≠ 0)
    (hu : ∀ i, u i ≠ 0)
    (hdual : MvPolynomial.eval u
      (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate) ≠ 0) :
    ‖fourierSum (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u‖ ≤
      2 * (p : ℝ) ^ (3 / 2 : ℝ) + 4 * (p : ℝ) := by
  rw [rpow_three_halves_eq_mul_sqrt (p : ℝ) (Nat.cast_nonneg p)]
  simpa only [mul_assoc] using
    diagonal_fourier_generic_bound_sqrt p hp a b u ha hpair hu hdual

end QuaternaryQuadraticForms
