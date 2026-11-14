import QuaternaryQuadraticForms.RankMinors
import QuaternaryQuadraticForms.QuadricSmooth
import Mathlib.Tactic.LinearCombination

/-!
# The geometric rank condition for diagonal quadratic pairs

The literal diagonal quadratic polynomials have gradient minors
`4 xᵢ xⱼ (aᵢ bⱼ - aⱼ bᵢ)`. Nonzero pair differences give the
projective rank-two condition. Conversely, a vanishing pair difference
produces a nonzero common zero over an algebraically closed field where
the rank is less than two. The coefficients of the second form may vanish.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Evaluation of the actual matrix polynomial of a diagonal form. -/
theorem eval_diagonalQuadraticPolynomial {K : Type*} [Field K]
    (a x : Fin 4 → K) :
    MvPolynomial.eval x (matrixQuadraticPolynomial (Matrix.diagonal a)) =
      ∑ i, a i * x i ^ 2 := by
  rw [eval_matrixQuadraticPolynomial]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual formal gradient of a diagonal quadratic polynomial. -/
theorem polynomialGradient_diagonalQuadraticPolynomial {K : Type*} [Field K]
    (a x : Fin 4 → K) :
    polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal a)) x =
      fun i => 2 * a i * x i := by
  rw [polynomialGradient_matrixQuadraticPolynomial _ (Matrix.diagonal_transpose a)]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  ring

/-- The two-by-two minors of the actual diagonal gradient rows. -/
theorem diagonal_gradient_minor {K : Type*} [Field K]
    (a b x : Fin 4 → K) (i j : Fin 4) :
    polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal a)) x i *
        polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal b)) x j -
      polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal a)) x j *
        polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal b)) x i =
      4 * (x i * x j) * (a i * b j - a j * b i) := by
  simp only [polynomialGradient_diagonalQuadraticPolynomial]
  ring

/-- Pairwise nonzero coefficient determinants imply the literal projective
rank-two condition for the two diagonal quadratic forms. -/
theorem diagonal_projectiveIntersectionTransverseRank {K : Type*} [Field K]
    (a b : Fin 4 → K) (h2 : (2 : K) ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hΔ : ∀ i j, i ≠ j → a i * b j - a j * b i ≠ 0) :
    ProjectiveIntersectionTransverseRank
      (matrixQuadraticPolynomial (Matrix.diagonal a))
      (matrixQuadraticPolynomial (Matrix.diagonal b)) := by
  intro x hx hF _
  by_contra hrank
  have hminors := (rank_two_ne_iff_minors_zero
    (polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal a)) x)
    (polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal b)) x)).mp hrank
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have hproduct (i j : Fin 4) (hij : i ≠ j) : x i * x j = 0 := by
    have hm := hminors i j
    rw [diagonal_gradient_minor] at hm
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (hΔ i j hij))).resolve_left h4
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, x i ≠ 0 := by
    by_contra! hzero
    exact hx (funext hzero)
  have hother (j : Fin 4) (hji : j ≠ i) : x j = 0 :=
    (mul_eq_zero.mp (hproduct i j hji.symm)).resolve_left hi
  have hvalue :
      MvPolynomial.eval x (matrixQuadraticPolynomial (Matrix.diagonal a)) =
        a i * x i ^ 2 := by
    rw [eval_diagonalQuadraticPolynomial]
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [hother j hji]
    · simp
  exact (mul_ne_zero (ha i) (pow_ne_zero 2 hi)) (hvalue.symm.trans hF)

private theorem eval_diagonal_two_coordinates {K : Type*} [Field K]
    (a : Fin 4 → K) (i j : Fin 4) (hij : i ≠ j) (z : K) :
    MvPolynomial.eval (Pi.single i 1 + Pi.single j z)
        (matrixQuadraticPolynomial (Matrix.diagonal a)) =
      a i + a j * z ^ 2 := by
  rw [eval_matrixQuadraticPolynomial, add_dotProduct, single_dotProduct,
    single_dotProduct]
  simp [Matrix.mulVec_diagonal, hij, hij.symm]
  ring

/-- A vanishing pair determinant gives an actual nonzero common zero with
rank failure over an algebraically closed field. The witness has coordinates
`xᵢ = 1`, `xⱼ² = -aᵢ/aⱼ`, and zero elsewhere. -/
theorem exists_diagonal_rank_failure_of_pair_eq_zero {K : Type*} [Field K]
    [IsAlgClosed K] (a b : Fin 4 → K) (ha : ∀ i, a i ≠ 0)
    (i j : Fin 4) (hij : i ≠ j) (hΔ : a i * b j - a j * b i = 0) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧
      MvPolynomial.eval x (matrixQuadraticPolynomial (Matrix.diagonal a)) = 0 ∧
      MvPolynomial.eval x (matrixQuadraticPolynomial (Matrix.diagonal b)) = 0 ∧
      Matrix.rank ![
        polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal a)) x,
        polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal b)) x] ≠ 2 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-a i / a j) (n := 2) (by decide)
  let x : Fin 4 → K := Pi.single i 1 + Pi.single j z
  have hxi : x i = 1 := by simp [x, hij]
  have hx : x ≠ 0 := by
    intro hzero
    have hi := congrFun hzero i
    exact one_ne_zero (by simpa only [hxi, Pi.zero_apply] using hi)
  have hF : MvPolynomial.eval x
      (matrixQuadraticPolynomial (Matrix.diagonal a)) = 0 := by
    dsimp only [x]
    rw [eval_diagonal_two_coordinates a i j hij z, hz]
    field_simp [ha j]
    ring
  have hG : MvPolynomial.eval x
      (matrixQuadraticPolynomial (Matrix.diagonal b)) = 0 := by
    dsimp only [x]
    rw [eval_diagonal_two_coordinates b i j hij z, hz]
    field_simp [ha j]
    linear_combination -hΔ
  have hratio : b j = b i / a i * a j := by
    field_simp [ha i]
    linear_combination hΔ
  have hrows :
      polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal b)) x =
        (b i / a i) •
          polynomialGradient (matrixQuadraticPolynomial (Matrix.diagonal a)) x := by
    funext k
    simp only [polynomialGradient_diagonalQuadraticPolynomial, Pi.smul_apply, smul_eq_mul]
    by_cases hki : k = i
    · subst k
      rw [hxi]
      field_simp [ha i]
    by_cases hkj : k = j
    · subst k
      rw [hratio]
      ring
    · have hxk : x k = 0 := by
        simp [x, hki, hkj]
      rw [hxk]
      ring
  refine ⟨x, hx, hF, hG, ?_⟩
  apply (rank_two_ne_iff_minors_zero _ _).mpr
  intro k l
  rw [hrows]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- A single vanishing pair determinant prevents geometric transversality
of the actual diagonal quadratic pair. -/
theorem not_diagonal_projectiveIntersectionTransverseRank_of_pair_eq_zero
    {K : Type*} [Field K] [IsAlgClosed K] (a b : Fin 4 → K)
    (ha : ∀ i, a i ≠ 0) (i j : Fin 4) (hij : i ≠ j)
    (hΔ : a i * b j - a j * b i = 0) :
    ¬ ProjectiveIntersectionTransverseRank
      (matrixQuadraticPolynomial (Matrix.diagonal a))
      (matrixQuadraticPolynomial (Matrix.diagonal b)) := by
  intro htrans
  obtain ⟨x, hx, hF, hG, hrank⟩ :=
    exists_diagonal_rank_failure_of_pair_eq_zero a b ha i j hij hΔ
  exact hrank (htrans x hx hF hG)

/-- Over an algebraically closed field of odd characteristic, the actual
projective rank condition is equivalent to nonvanishing of all pair
determinants, provided the first diagonal form is nonsingular. -/
theorem diagonal_projectiveIntersectionTransverseRank_iff {K : Type*} [Field K]
    [IsAlgClosed K] (a b : Fin 4 → K) (h2 : (2 : K) ≠ 0)
    (ha : ∀ i, a i ≠ 0) :
    ProjectiveIntersectionTransverseRank
        (matrixQuadraticPolynomial (Matrix.diagonal a))
        (matrixQuadraticPolynomial (Matrix.diagonal b)) ↔
      ∀ i j, i ≠ j → a i * b j - a j * b i ≠ 0 := by
  constructor
  · intro htrans i j hij hΔ
    exact not_diagonal_projectiveIntersectionTransverseRank_of_pair_eq_zero
      a b ha i j hij hΔ htrans
  · exact diagonal_projectiveIntersectionTransverseRank a b h2 ha

end QuaternaryQuadraticForms
