import QuaternaryQuadraticForms.FourierRays

/-!
# The polynomial of a matrix quadratic form

The power-sum argument in Lemma 5.9 applies to multivariate polynomials.  This
file identifies the manuscript's literal expression `xᵀ A x` with the
evaluation of a homogeneous polynomial of degree two.  The degree bound is
proved for that polynomial, including when some coefficients vanish after
reduction modulo the prime.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- The polynomial whose evaluation is the matrix quadratic form. -/
def matrixQuadraticPolynomial (A : Matrix ι ι R) : MvPolynomial ι R :=
  ∑ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X i * MvPolynomial.X j

/-- Evaluation agrees with the actual matrix expression, for arbitrary
coefficients in a commutative semiring. -/
theorem eval_matrixQuadraticPolynomial (A : Matrix ι ι R) (x : ι → R) :
    MvPolynomial.eval x (matrixQuadraticPolynomial A) = dotProduct x (A.mulVec x) := by
  simp only [matrixQuadraticPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ac_rfl

/-- Every monomial in the matrix quadratic polynomial has degree two. -/
theorem matrixQuadraticPolynomial_homogeneous (A : Matrix ι ι R) :
    (matrixQuadraticPolynomial A).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact (MvPolynomial.isHomogeneous_C_mul_X (A i j) i).mul
    (MvPolynomial.isHomogeneous_X R j)

/-- The total-degree hypothesis used in the affine power-sum argument. -/
theorem matrixQuadraticPolynomial_totalDegree_le (A : Matrix ι ι R) :
    (matrixQuadraticPolynomial A).totalDegree ≤ 2 :=
  (matrixQuadraticPolynomial_homogeneous A).totalDegree_le

/-- The exact four-coordinate prime-field specialization used by the
manuscript's Fourier and character sums. -/
theorem eval_matrixQuadraticPolynomial_quadraticValue {p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) (ZMod p)) (x : PrimeVector p) :
    MvPolynomial.eval x (matrixQuadraticPolynomial A) = quadraticValue A x :=
  eval_matrixQuadraticPolynomial A x

end QuaternaryQuadraticForms
