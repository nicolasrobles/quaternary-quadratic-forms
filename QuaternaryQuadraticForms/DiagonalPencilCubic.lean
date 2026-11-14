import QuaternaryQuadraticForms.DiagonalPencil

/-!
# The cubic pencil and the literal dual quadratic form

The degree bound and leading coefficient are identities of formal polynomials.
The leading coefficient is the adjugate matrix quadratic form of `F`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem pencilLinear_natDegree_le {R : Type*} [CommRing R] (a b : R) :
    (Polynomial.C b + Polynomial.X * Polynomial.C a).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_C_add]
  exact (Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le

private theorem pencilComplement_natDegree_le {R : Type*} [CommRing R]
    (a b : Fin 4 → R) (i : Fin 4) :
    (∏ j ∈ Finset.univ.erase i,
      (Polynomial.C (b j) + Polynomial.X * Polynomial.C (a j))).natDegree ≤ 3 := by
  have hbound : (∑ j ∈ Finset.univ.erase i,
      (Polynomial.C (b j) + Polynomial.X * Polynomial.C (a j)).natDegree) ≤
      ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro j _
    exact pencilLinear_natDegree_le (a j) (b j)
  have hcard : (∑ _j ∈ Finset.univ.erase i, (1 : ℕ)) = 3 := by simp
  exact (Polynomial.natDegree_prod_le (Finset.univ.erase i)
    (fun j : Fin 4 => Polynomial.C (b j) + Polynomial.X * Polynomial.C (a j))).trans
      (hbound.trans_eq hcard)

/-- The actual source pencil polynomial has degree at most three over every
commutative coefficient ring. -/
theorem diagonalPencilPhi_natDegree_le {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) : (diagonalPencilPhi a b u).natDegree ≤ 3 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (pencilComplement_natDegree_le a b i)

private theorem pencilComplement_coeff_three {R : Type*} [CommRing R]
    (a b : Fin 4 → R) (i : Fin 4) :
    (∏ j ∈ Finset.univ.erase i,
      (Polynomial.C (b j) + Polynomial.X * Polynomial.C (a j))).coeff 3 =
        ∏ j ∈ Finset.univ.erase i, a j := by
  simpa using Polynomial.coeff_prod_of_natDegree_le (Finset.univ.erase i)
    (fun j => Polynomial.C (b j) + Polynomial.X * Polynomial.C (a j)) 1
    (fun j _ => pencilLinear_natDegree_le (a j) (b j))

/-- The cubic coefficient is exactly `F*(u)`, evaluated using the adjugate
of the actual diagonal matrix of `F`. -/
theorem diagonalPencilPhi_coeff_three {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) :
    (diagonalPencilPhi a b u).coeff 3 =
      dotProduct u ((Matrix.diagonal a).adjugate.mulVec u) := by
  simp only [diagonalPencilPhi, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    pencilComplement_coeff_three, Matrix.adjugate_diagonal, dotProduct,
    Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The same leading coefficient equals evaluation of the literal dual
matrix polynomial, not merely a separate numerical expression. -/
theorem diagonalPencilPhi_coeff_three_eq_eval {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) :
    (diagonalPencilPhi a b u).coeff 3 =
      MvPolynomial.eval u (matrixQuadraticPolynomial (Matrix.diagonal a).adjugate) := by
  rw [eval_matrixQuadraticPolynomial, diagonalPencilPhi_coeff_three]

/-- At each parameter, `Φ_u(t)` is the dual quadratic form of `G + t F`. -/
theorem eval_diagonalPencilPhi_eq_dual {R : Type*} [CommRing R]
    (a b u : Fin 4 → R) (t : R) :
    (diagonalPencilPhi a b u).eval t =
      dotProduct u ((Matrix.diagonal (diagonalPencilCoeff a b t)).adjugate.mulVec u) := by
  rw [eval_diagonalPencilPhi, Matrix.adjugate_diagonal]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Nonvanishing of the actual dual value makes the pencil genuinely cubic. -/
theorem diagonalPencilPhi_natDegree_eq_three {R : Type*} [CommRing R]
    (a b u : Fin 4 → R)
    (hdual : dotProduct u ((Matrix.diagonal a).adjugate.mulVec u) ≠ 0) :
    (diagonalPencilPhi a b u).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (diagonalPencilPhi_natDegree_le a b u)
  rwa [diagonalPencilPhi_coeff_three]

end QuaternaryQuadraticForms
