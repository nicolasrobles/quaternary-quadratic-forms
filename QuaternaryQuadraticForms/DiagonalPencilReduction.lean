import QuaternaryQuadraticForms.DiagonalPencil

/-!
# Reduction of the source diagonal-pencil hypotheses

The literal prime restriction `p ∤ 2 α M` supplies every field hypothesis
used in the pencil calculation. The generic-frequency condition reduces
to nonzero coordinates and the actual adjugate quadratic form.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal source good-prime restriction supplies odd characteristic,
nonzero first coefficients, and all nonzero pair differences after reduction. -/
theorem diagonalPencil_reduced_data (p : ℕ) [Fact p.Prime]
    (a b : Fin 4 → ℤ)
    (hp : ¬ (p : ℤ) ∣ 2 * (∏ i, a i) * diagonalPairProduct a b) :
    p ≠ 2 ∧ (∀ i, (a i : ZMod p) ≠ 0) ∧
      ∀ i j : Fin 4, i ≠ j →
        (a i : ZMod p) * (b j : ZMod p) - (a j : ZMod p) * (b i : ZMod p) ≠ 0 := by
  have hcast : ((2 * (∏ i, a i) * diagonalPairProduct a b : ℤ) : ZMod p) ≠ 0 :=
    fun h => hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  have hproduct : (2 : ZMod p) * (∏ i, (a i : ZMod p)) *
      ((diagonalPairProduct a b : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_prod] using hcast
  obtain ⟨hfirst, hM⟩ := mul_ne_zero_iff.mp hproduct
  obtain ⟨h2, hα⟩ := mul_ne_zero_iff.mp hfirst
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact h2 (ZMod.natCast_self 2)
  refine ⟨hp2, diagonal_coefficients_ne_zero _ hα, ?_⟩
  have hM' : diagonalPairProduct
      (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p)) ≠ 0 := by
    intro hz
    apply hM
    exact (diagonalPairProduct_map (Int.castRingHom (ZMod p)) a b).symm.trans hz
  exact diagonal_pair_difference_ne_zero _ _
    ((diagonalPairProduct_ne_zero_iff _ _).mp hM')

/-- Coefficient maps preserve the actual adjugate dual value of the first
diagonal form. -/
theorem diagonalPencil_dual_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a u : Fin 4 → R) :
    MvPolynomial.eval (f ∘ u)
        (matrixQuadraticPolynomial (Matrix.diagonal (f ∘ a)).adjugate) =
      f (MvPolynomial.eval u (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate)) := by
  simp only [eval_matrixQuadraticPolynomial, Matrix.adjugate_diagonal,
    Matrix.mulVec_diagonal, dotProduct, Function.comp_apply, map_sum, map_prod, map_mul]

/-- The literal generic-frequency nondivisibility gives the needed nonzero
coordinates and nonzero dual value in the prime field. -/
theorem diagonalPencil_generic_reduction (p : ℕ) [Fact p.Prime]
    (a u : Fin 4 → ℤ)
    (hu : ¬ (p : ℤ) ∣
      MvPolynomial.eval u (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate) *
        ∏ i, u i) :
    (∀ i, (u i : ZMod p) ≠ 0) ∧
      MvPolynomial.eval (fun i => (u i : ZMod p))
        (matrixQuadraticPolynomial (Matrix.diagonal (fun i => (a i : ZMod p))).adjugate) ≠ 0 := by
  have hcast : ((MvPolynomial.eval u
      (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate) * ∏ i, u i : ℤ) :
        ZMod p) ≠ 0 := fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  have hproduct :
      (MvPolynomial.eval u (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate) : ZMod p) *
        (∏ i, (u i : ZMod p)) ≠ 0 := by
    simpa only [Int.cast_mul, Int.cast_prod] using hcast
  obtain ⟨hdual, hcoords⟩ := mul_ne_zero_iff.mp hproduct
  refine ⟨diagonal_coefficients_ne_zero _ hcoords, ?_⟩
  intro hz
  apply hdual
  exact (diagonalPencil_dual_map (Int.castRingHom (ZMod p)) a u).symm.trans hz

end QuaternaryQuadraticForms
