import QuaternaryQuadraticForms.QuadraticGaussSums
import QuaternaryQuadraticForms.PrimeQuadraticGauss
import QuaternaryQuadraticForms.FourierOrthogonality
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Prime-field Gauss evaluation for a general quaternary matrix

An actual orthogonal basis diagonalizes the symmetric matrix. The
change-of-basis determinant is retained, so its square disappears under
the quadratic character. The finite sum is then evaluated by the proved
one-dimensional quadratic Gauss identity.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

private theorem symmetric_orthogonal_basis (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) :
    ∃ b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p),
      ∀ i j, i ≠ j → Matrix.toBilin' A (b i) (b j) = 0 := by
  letI : Invertible (2 : ZMod p) :=
    invertibleOfNonzero (Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp))
  have hsym : LinearMap.IsSymm (Matrix.toBilin' A) := by
    rw [LinearMap.isSymm_def]
    intro x y
    change Matrix.toBilin' A x y = Matrix.toBilin' A y x
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsym
  have hd : Module.finrank (ZMod p) (Fin 4 → ZMod p) = 4 :=
    Module.finrank_fin_fun (ZMod p)
  refine ⟨b.reindex (finCongr hd), fun i j hij => ?_⟩
  simp only [Module.Basis.reindex_apply]
  exact hb (fun h => hij ((finCongr hd).symm.injective h))

private theorem orthogonal_basis_matrix
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p))
    (hb : ∀ i j, i ≠ j → Matrix.toBilin' A (b i) (b j) = 0) :
    BilinForm.toMatrix b (Matrix.toBilin' A) =
      Matrix.diagonal (fun i => Matrix.toBilin' A (b i) (b i)) := by
  ext i j
  rw [BilinForm.toMatrix_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact hb i j hij

private theorem basis_diagonal_quadratic_value
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p))
    (hb : ∀ i j, i ≠ j → Matrix.toBilin' A (b i) (b j) = 0)
    (x : Fin 4 → ZMod p) :
    dotProduct (b.equivFun.symm x) (A.mulVec (b.equivFun.symm x)) =
      ∑ i, Matrix.toBilin' A (b i) (b i) * x i ^ 2 := by
  rw [← Matrix.toBilin'_apply', ← BilinForm.dotProduct_toMatrix_mulVec b,
    orthogonal_basis_matrix p A b hb]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem orthogonal_basis_det
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p))
    (hb : ∀ i j, i ≠ j → Matrix.toBilin' A (b i) (b j) = 0) :
    (∏ i, Matrix.toBilin' A (b i) (b i)) =
      ((Pi.basisFun (ZMod p) (Fin 4)).toMatrix b).det ^ 2 * A.det := by
  let P := (Pi.basisFun (ZMod p) (Fin 4)).toMatrix b
  have hm : P.transpose * A * P =
      Matrix.diagonal (fun i => Matrix.toBilin' A (b i) (b i)) := by
    simpa only [P, BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix'_toBilin', orthogonal_basis_matrix p A b hb] using
      BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun (ZMod p) (Fin 4)) b
        (Matrix.toBilin' A)
  calc
    (∏ i, Matrix.toBilin' A (b i) (b i)) =
        (Matrix.diagonal (fun i => Matrix.toBilin' A (b i) (b i))).det :=
      Matrix.det_diagonal.symm
    _ = (P.transpose * A * P).det := congrArg Matrix.det hm.symm
    _ = P.det ^ 2 * A.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring

private theorem basis_matrix_det_ne_zero
    (p : ℕ) [Fact p.Prime]
    (b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p)) :
    ((Pi.basisFun (ZMod p) (Fin 4)).toMatrix b).det ≠ 0 :=
  (Matrix.isUnit_det_of_right_inverse
    ((Pi.basisFun (ZMod p) (Fin 4)).toMatrix_mul_toMatrix_flip b)).ne_zero

private theorem orthogonal_basis_coeff_ne_zero
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (hdet : A.det ≠ 0)
    (b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p))
    (hb : ∀ i j, i ≠ j → Matrix.toBilin' A (b i) (b j) = 0) (i : Fin 4) :
    Matrix.toBilin' A (b i) (b i) ≠ 0 := by
  have hprod : (∏ j, Matrix.toBilin' A (b j) (b j)) ≠ 0 := by
    rw [orthogonal_basis_det p A b hb]
    exact mul_ne_zero (pow_ne_zero _ (basis_matrix_det_ne_zero p b)) hdet
  exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

private theorem orthogonal_basis_char_det
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) (ZMod p))
    (b : Module.Basis (Fin 4) (ZMod p) (Fin 4 → ZMod p))
    (hb : ∀ i j, i ≠ j → Matrix.toBilin' A (b i) (b j) = 0) :
    complexQuadraticChar p (∏ i, Matrix.toBilin' A (b i) (b i)) =
      complexQuadraticChar p A.det := by
  rw [orthogonal_basis_det p A b hb, map_mul, map_pow,
    complexQuadraticChar_sq_apply p _ (basis_matrix_det_ne_zero p b), one_mul]

private theorem diagonal_pure_gauss
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (d : Fin 4 → ZMod p) (hd : ∀ i, d i ≠ 0)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x : Fin 4 → ZMod p, ZMod.stdAddChar (a * ∑ i, d i * x i ^ 2)) =
      complexQuadraticChar p (∏ i, d i) * (p : ℂ) ^ 2 := by
  classical
  have hphase (x : Fin 4 → ZMod p) :
      a * (∑ i, d i * x i ^ 2) = ∑ i, (a * d i) * x i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hscalar (i : Fin 4) :
      (∑ y : ZMod p, ZMod.stdAddChar ((a * d i) * y ^ 2)) =
        complexQuadraticChar p (a * d i) * primeQuadraticGauss p :=
    primeQuadraticExponentialSum_unshifted p hp (a * d i) (mul_ne_zero ha (hd i))
  calc
    (∑ x : Fin 4 → ZMod p, ZMod.stdAddChar (a * ∑ i, d i * x i ^ 2)) =
        ∑ x : Fin 4 → ZMod p, ∏ i, ZMod.stdAddChar ((a * d i) * x i ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hphase]
      exact stdAddChar_sum p Finset.univ _
    _ = ∏ i : Fin 4, ∑ y : ZMod p, ZMod.stdAddChar ((a * d i) * y ^ 2) :=
      (Fintype.prod_sum (fun (i : Fin 4) (y : ZMod p) =>
        ZMod.stdAddChar ((a * d i) * y ^ 2))).symm
    _ = ∏ i : Fin 4, (complexQuadraticChar p (a * d i) * primeQuadraticGauss p) := by
      apply Finset.prod_congr rfl
      intro i _
      exact hscalar i
    _ = (∏ i : Fin 4, complexQuadraticChar p (a * d i)) * primeQuadraticGauss p ^ 4 := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = complexQuadraticChar p (∏ i, d i) * (p : ℂ) ^ 2 := by
      rw [primeQuadraticGauss_fourth p hp, ← map_prod (complexQuadraticChar p)]
      simp only [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, map_mul, map_pow]
      have hfour : complexQuadraticChar p a ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul,
          complexQuadraticChar_sq_apply p a ha, one_pow]
      rw [hfour, one_mul]

/-- The exact pure Gauss evaluation for every nonsingular symmetric
quaternary matrix over an odd prime field and every nonzero scalar. -/
theorem quadraticGaussSum_prime_zero_frequency
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (a : ZMod p) (ha : a ≠ 0) :
    quadraticGaussSum p A a 0 = complexQuadraticChar p A.det * (p : ℂ) ^ 2 := by
  obtain ⟨b, hb⟩ := symmetric_orthogonal_basis p hp A hA
  unfold quadraticGaussSum
  simp only [zero_dotProduct, add_zero]
  calc
    (∑ x : Fin 4 → ZMod p, ZMod.stdAddChar (a * dotProduct x (A.mulVec x))) =
        ∑ x : Fin 4 → ZMod p,
          ZMod.stdAddChar
            (a * dotProduct (b.equivFun.symm x) (A.mulVec (b.equivFun.symm x))) :=
      (Equiv.sum_comp b.equivFun.symm.toEquiv
        (fun x : Fin 4 → ZMod p => ZMod.stdAddChar (a * dotProduct x (A.mulVec x)))).symm
    _ = ∑ x : Fin 4 → ZMod p,
          ZMod.stdAddChar (a * ∑ i, Matrix.toBilin' A (b i) (b i) * x i ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [basis_diagonal_quadratic_value p A b hb x]
    _ = complexQuadraticChar p (∏ i, Matrix.toBilin' A (b i) (b i)) * (p : ℂ) ^ 2 :=
      diagonal_pure_gauss p hp _ (orthogonal_basis_coeff_ne_zero p A hdet b hb) a ha
    _ = complexQuadraticChar p A.det * (p : ℂ) ^ 2 := by
      rw [orthogonal_basis_char_det p A b hb]

/-- The same exact prime-field evaluation with the zero scalar retained;
this is the scalar sum required for the affine quadric point count. -/
theorem quadraticGaussSum_prime_all_scalars
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (a : ZMod p) :
    quadraticGaussSum p A a 0 =
      if a = 0 then (p : ℂ) ^ 4 else complexQuadraticChar p A.det * (p : ℂ) ^ 2 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [quadraticGaussSum, ZMod.card]
  · rw [if_neg ha]
    exact quadraticGaussSum_prime_zero_frequency p hp A hA hdet a ha

end QuaternaryQuadraticForms
