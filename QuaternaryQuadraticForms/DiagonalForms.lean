import QuaternaryQuadraticForms.BadReductionSystem

/-!
# The diagonal coefficients and their pair product

The source quantity `M` is the product of exactly the six differences
`a_i b_j - a_j b_i` with `i < j`. Its definition, coefficient maps and
nonvanishing are kept separate from the geometric rank argument.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The literal diagonal matrix polynomial is the source sum of four
coefficient-weighted squares, as an identity of formal polynomials. -/
theorem diagonalQuadraticPolynomial_eq_sum {R : Type*} [CommRing R]
    (a : Fin 4 → R) :
    matrixQuadraticPolynomial (Matrix.diagonal a) =
      ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i ^ 2 := by
  classical
  unfold matrixQuadraticPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [pow_two, mul_assoc]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- The literal six-factor product `M` in the diagonal case. -/
def diagonalPairProduct {R : Type*} [CommRing R] (a b : Fin 4 → R) : R :=
  ∏ i : Fin 4, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (a i * b j - a j * b i)

/-- Coefficient homomorphisms preserve the actual pair product. -/
theorem diagonalPairProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : Fin 4 → R) :
    diagonalPairProduct (f ∘ a) (f ∘ b) = f (diagonalPairProduct a b) := by
  simp [diagonalPairProduct, map_prod, Function.comp_apply]

/-- The product is nonzero exactly when all six source differences are
nonzero. No individual condition on the coefficients of the second form
is imposed. -/
theorem diagonalPairProduct_ne_zero_iff {R : Type*} [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] (a b : Fin 4 → R) :
    diagonalPairProduct a b ≠ 0 ↔
      ∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0 := by
  simp [diagonalPairProduct, Finset.prod_ne_zero_iff]

/-- The six ordered-by-size differences control every pair of distinct
indices, because reversing the pair only changes its sign. -/
theorem diagonal_pair_difference_ne_zero {R : Type*} [CommRing R]
    (a b : Fin 4 → R)
    (h : ∀ i j : Fin 4, i < j → a i * b j - a j * b i ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) : a i * b j - a j * b i ≠ 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact h i j hlt
  · rw [show a i * b j - a j * b i = -(a j * b i - a i * b j) by ring]
    exact neg_ne_zero.mpr (h j i hgt)

/-- The literal matrix polynomial of a diagonal form commutes with every
coefficient map, including integer reduction and algebraic closure. -/
theorem diagonalQuadraticPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 4 → R) :
    (matrixQuadraticPolynomial (Matrix.diagonal a)).map f =
      matrixQuadraticPolynomial (Matrix.diagonal (f ∘ a)) := by
  rw [matrixQuadraticPolynomial_map_ring]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Nonsingularity of the diagonal coefficient product supplies every
nonzero first-form coefficient. -/
theorem diagonal_coefficients_ne_zero {R : Type*} [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] (a : Fin 4 → R)
    (hα : (∏ i, a i) ≠ 0) : ∀ i, a i ≠ 0 := by
  simpa only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left] using hα

/-- The actual quadratic bad-prime modulus is `2 |α|` for the source
coefficient product `α = ∏ a_i`. -/
theorem quadraticBadPrimeModulus_diagonal (a : Fin 4 → ℤ) :
    quadraticBadPrimeModulus (Matrix.diagonal a) = 2 * (∏ i, a i).natAbs := by
  simp only [quadraticBadPrimeModulus, Matrix.det_diagonal]

/-- The natural-number product used in the modulus calculation is the
absolute value of the source integer `2 α M`, allowing either sign. -/
theorem diagonal_bad_modulus_product (a b : Fin 4 → ℤ) :
    quadraticBadPrimeModulus (Matrix.diagonal a) * (diagonalPairProduct a b).natAbs =
      (2 * (∏ i, a i) * diagonalPairProduct a b).natAbs := by
  rw [quadraticBadPrimeModulus_diagonal]
  norm_num [Int.natAbs_mul]

end QuaternaryQuadraticForms
