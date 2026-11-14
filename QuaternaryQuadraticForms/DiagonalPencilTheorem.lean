import QuaternaryQuadraticForms.DiagonalPencilConsequences
import QuaternaryQuadraticForms.DiagonalPencilReduction

/-!
# Complete Lemma 4.6 for the source integral data

The final statements use the existing integral Fourier sum and integer
projective trace. Every finite-field hypothesis follows from the literal
prime restriction, and the generic condition uses the actual adjugate
quadratic form. No separate nonvanishing or separability premise is added.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The exact pencil formula for the actual integral input data, with
literal divisibility in the singular-member filter. -/
theorem integral_diagonal_fourier_pencil_formula (p : ℕ) [Fact p.Prime]
    (a b u : Fin 4 → ℤ)
    (hp : ¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b) :
    integralFourierSum p (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u =
      (p : ℂ) * (∑ t ∈ Finset.univ \ diagonalPencilRoots
          (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p)),
        complexQuadraticChar p
          (-((diagonalPencilPhi a b u).map (Int.castRingHom (ZMod p))).eval t)) +
      (p : ℂ) * (∑ i ∈ Finset.univ.filter (fun i => (p : ℤ) ∣ u i),
        complexQuadraticChar p ((diagonalKappa a b i : ℤ) : ZMod p) *
          primeRamanujan p ((diagonalPencilNu a b u i : ℤ) : ZMod p)) := by
  classical
  obtain ⟨hp2, ha, hpair⟩ := diagonalPencil_reduced_data p a b hp
  have hformula := diagonal_fourier_pencil_formula p hp2
    (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p))
    (fun i => (u i : ZMod p)) ha hpair
  have hphi := diagonalPencilPhi_map (Int.castRingHom (ZMod p)) a b u
  have hkappa (i : Fin 4) : diagonalKappa
      (fun j => (a j : ZMod p)) (fun j => (b j : ZMod p)) i =
        ((diagonalKappa a b i : ℤ) : ZMod p) :=
    diagonalKappa_map (Int.castRingHom (ZMod p)) a b i
  have hnu (i : Fin 4) : diagonalPencilNu
      (fun j => (a j : ZMod p)) (fun j => (b j : ZMod p))
      (fun j => (u j : ZMod p)) i = ((diagonalPencilNu a b u i : ℤ) : ZMod p) :=
    diagonalPencilNu_map (Int.castRingHom (ZMod p)) a b u i
  unfold integralFourierSum
  rw [Matrix.diagonal_map (map_zero (Int.castRingHom (ZMod p))),
    diagonalQuadraticPolynomial_map]
  simpa only [reduceFrequency, hphi, Function.comp_apply, hkappa, hnu,
    ZMod.intCast_zmod_eq_zero_iff_dvd] using hformula

/-- The source trace identity as an equality of the actual integer sums. -/
theorem integral_diagonal_projectiveTrace_eq (p : ℕ) [Fact p.Prime]
    (a b : Fin 4 → ℤ)
    (hp : ¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b) :
    integralProjectiveQuadraticTrace p (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) =
      (p : ℤ) * ∑ i : Fin 4,
        quadraticChar (ZMod p) ((diagonalKappa a b i : ℤ) : ZMod p) := by
  obtain ⟨hp2, ha, hpair⟩ := diagonalPencil_reduced_data p a b hp
  have htrace := diagonal_projectiveQuadraticTrace_eq p hp2
    (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p)) ha hpair
  have hkappa (i : Fin 4) : diagonalKappa
      (fun j => (a j : ZMod p)) (fun j => (b j : ZMod p)) i =
        ((diagonalKappa a b i : ℤ) : ZMod p) :=
    diagonalKappa_map (Int.castRingHom (ZMod p)) a b i
  unfold integralProjectiveQuadraticTrace
  rw [Matrix.diagonal_map (map_zero (Int.castRingHom (ZMod p))),
    diagonalQuadraticPolynomial_map]
  simpa only [Function.comp_apply, hkappa] using htrace

/-- The generic bound under the literal source nondivisibility of
`F*(u) u_1 u_2 u_3 u_4`, including all cubic multiplicity cases. -/
theorem integral_diagonal_fourier_bound (p : ℕ) [Fact p.Prime]
    (a b u : Fin 4 → ℤ)
    (hp : ¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b)
    (hu : ¬ (p : ℤ) ∣
      dotProduct u ((Matrix.diagonal a).adjugate.mulVec u) * ∏ i, u i) :
    ‖integralFourierSum p (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u‖ ≤
      2 * (p : ℝ) ^ (3 / 2 : ℝ) + 4 * (p : ℝ) := by
  obtain ⟨hp2, ha, hpair⟩ := diagonalPencil_reduced_data p a b hp
  obtain ⟨hcoords, hdual⟩ := diagonalPencil_generic_reduction p a u
    (by simpa only [eval_matrixQuadraticPolynomial] using hu)
  have hbound := diagonal_fourier_generic_bound p hp2
    (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p))
    (fun i => (u i : ZMod p)) ha hpair hcoords hdual
  unfold integralFourierSum
  rw [Matrix.diagonal_map (map_zero (Int.castRingHom (ZMod p))),
    diagonalQuadraticPolynomial_map]
  simpa only [reduceFrequency, Function.comp_apply] using hbound

/-- Every clause of Lemma 4.6: the exact pencil formula, integer projective
trace, and generic Fourier bound, all for the source integral data. -/
theorem diagonal_pencil (p : ℕ) [Fact p.Prime]
    (a b u : Fin 4 → ℤ)
    (hp : ¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b) :
    (integralFourierSum p (Matrix.diagonal a) (complexQuadraticChar p)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) u =
      (p : ℂ) * (∑ t ∈ Finset.univ \ diagonalPencilRoots
          (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p)),
        complexQuadraticChar p
          (-((diagonalPencilPhi a b u).map (Int.castRingHom (ZMod p))).eval t)) +
      (p : ℂ) * (∑ i ∈ Finset.univ.filter (fun i => (p : ℤ) ∣ u i),
        complexQuadraticChar p ((diagonalKappa a b i : ℤ) : ZMod p) *
          primeRamanujan p ((diagonalPencilNu a b u i : ℤ) : ZMod p))) ∧
    (integralProjectiveQuadraticTrace p (Matrix.diagonal a)
        (matrixQuadraticPolynomial (Matrix.diagonal b)) =
      (p : ℤ) * ∑ i : Fin 4,
        quadraticChar (ZMod p) ((diagonalKappa a b i : ℤ) : ZMod p)) ∧
    (¬ (p : ℤ) ∣ dotProduct u ((Matrix.diagonal a).adjugate.mulVec u) * ∏ i, u i →
      ‖integralFourierSum p (Matrix.diagonal a) (complexQuadraticChar p)
          (matrixQuadraticPolynomial (Matrix.diagonal b)) u‖ ≤
        2 * (p : ℝ) ^ (3 / 2 : ℝ) + 4 * (p : ℝ)) :=
  ⟨integral_diagonal_fourier_pencil_formula p a b u hp,
    integral_diagonal_projectiveTrace_eq p a b hp,
    integral_diagonal_fourier_bound p a b u hp⟩

end QuaternaryQuadraticForms
