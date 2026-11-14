import QuaternaryQuadraticForms.ConicParametrization
import QuaternaryQuadraticForms.TransversalityRank
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# The smoothness of the actual projective quadric

The gradient is calculated from the literal matrix polynomial. For a
symmetric matrix it is `2 A x`, so nonsingularity of the matrix in odd
characteristic excludes every nonzero singular vector. The same statement
holds after any extension of the coefficient field.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The projective Jacobian condition for one homogeneous equation, written
on its actual nonzero affine representatives. -/
def ProjectiveHypersurfaceSmooth {K : Type*} [Field K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) : Prop :=
  ∀ x : Fin N → K, x ≠ 0 → MvPolynomial.eval x F = 0 → polynomialGradient F x ≠ 0

/-- A formal partial derivative of the matrix quadratic polynomial evaluates
to the sum of the corresponding row and column pairings. -/
theorem eval_pderiv_matrixQuadraticPolynomial {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (i : ι) (x : ι → K) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (matrixQuadraticPolynomial A)) =
      A.mulVec x i + A.transpose.mulVec x i := by
  classical
  simp [matrixQuadraticPolynomial, Pi.single_apply, Finset.sum_add_distrib,
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_ite, mul_comm, add_comm]

/-- For a symmetric matrix, the actual formal gradient is twice `A x`. -/
theorem polynomialGradient_matrixQuadraticPolynomial {K ι : Type*}
    [Field K] [Fintype ι] (A : Matrix ι ι K) (hA : A.transpose = A) (x : ι → K) :
    polynomialGradient (matrixQuadraticPolynomial A) x = (2 : K) • A.mulVec x := by
  funext i
  rw [polynomialGradient, eval_pderiv_matrixQuadraticPolynomial, hA]
  simp [two_mul]

/-- A nonsingular symmetric quadratic matrix in odd characteristic has no
nonzero vector at which all formal partial derivatives vanish. -/
theorem matrixQuadratic_gradient_ne_zero {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (h2 : (2 : K) ≠ 0) (x : ι → K) (hx : x ≠ 0) :
    polynomialGradient (matrixQuadraticPolynomial A) x ≠ 0 := by
  classical
  rw [polynomialGradient_matrixQuadraticPolynomial A hA]
  intro h
  apply hx
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet ((smul_eq_zero.mp h).resolve_left h2)

/-- The nonsingular matrix implies the literal projective Jacobian condition. -/
theorem matrixQuadratic_projective_smooth {K : Type*} [Field K] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) K) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (h2 : (2 : K) ≠ 0) : ProjectiveHypersurfaceSmooth (matrixQuadraticPolynomial A) := by
  intro x hx _
  exact matrixQuadratic_gradient_ne_zero A hA hdet h2 x hx

/-- A nonsingular symmetric matrix remains so after extending its field. -/
theorem matrixQuadratic_projective_smooth_map {K L : Type*} [Field K] [Field L] {N : ℕ}
    (f : K →+* L) (A : Matrix (Fin N) (Fin N) K)
    (hA : A.transpose = A) (hdet : A.det ≠ 0) (h2 : (2 : K) ≠ 0) :
    ProjectiveHypersurfaceSmooth ((matrixQuadraticPolynomial A).map f) := by
  have hmap : (matrixQuadraticPolynomial A).map f = matrixQuadraticPolynomial (A.map f) := by
    simp only [matrixQuadraticPolynomial, map_sum, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_X, Matrix.map_apply]
  rw [hmap]
  apply matrixQuadratic_projective_smooth
  · exact congrArg (fun M : Matrix (Fin N) (Fin N) K => M.map f) hA
  · intro h
    exact hdet (f.injective ((f.map_det A).trans (h.trans f.map_zero.symm)))
  · intro h
    apply h2
    apply f.injective
    simpa only [map_ofNat, map_zero] using h

/-- The actual quadric polynomial is nonzero under the nonsingularity and
odd-characteristic hypotheses. -/
theorem matrixQuadraticPolynomial_ne_zero {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (h2 : (2 : K) ≠ 0) : matrixQuadraticPolynomial A ≠ 0 := by
  have hx : (Pi.single 0 (1 : K) : Fin 4 → K) ≠ 0 := by simp
  intro h
  have hg := matrixQuadratic_gradient_ne_zero A hA hdet h2 _ hx
  apply hg
  funext i
  change MvPolynomial.eval _ (MvPolynomial.pderiv i (matrixQuadraticPolynomial A)) = 0
  rw [h]
  simp

/-- The nonsingular matrix polynomial has the exact degree two. -/
theorem matrixQuadraticPolynomial_totalDegree {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (h2 : (2 : K) ≠ 0) : (matrixQuadraticPolynomial A).totalDegree = 2 :=
  (matrixQuadraticPolynomial_homogeneous A).totalDegree
    (matrixQuadraticPolynomial_ne_zero A hA hdet h2)

private theorem finsupp_eq_single_of_degree_le_one {ι : Type*}
    (m : ι →₀ ℕ) (hm : m.degree ≤ 1) (i : ι) (hi : m i ≠ 0) :
    m = Finsupp.single i 1 := by
  have hle : Finsupp.single i 1 ≤ m :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hd : (m - Finsupp.single i 1).degree + 1 = m.degree := by
    calc
      _ = (m - Finsupp.single i 1 + Finsupp.single i 1).degree := by simp
      _ = m.degree := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  have hz : m - Finsupp.single i 1 = 0 :=
    (Finsupp.degree_eq_zero_iff _).mp (by omega)
  exact le_antisymm (tsub_eq_zero_iff_le.mp hz) hle

/-- Every formal derivative of an affine-linear polynomial is constant as a
function of its evaluation point. -/
theorem eval_pderiv_eq_of_totalDegree_le_one {K ι : Type*} [Field K]
    (P : MvPolynomial ι K) (hP : P.totalDegree ≤ 1) (i : ι) (x y : ι → K) :
    MvPolynomial.eval x (MvPolynomial.pderiv i P) =
      MvPolynomial.eval y (MvPolynomial.pderiv i P) := by
  classical
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : m.degree ≤ 1 := (MvPolynomial.le_totalDegree hm).trans hP
  by_cases hi : m i = 0
  · simp [MvPolynomial.pderiv_monomial, hi]
  · rw [finsupp_eq_single_of_degree_le_one m hd i hi]
    simp

/-- The actual gradient of an affine-linear polynomial is the same at every
point, including the origin. -/
theorem polynomialGradient_eq_of_totalDegree_le_one {K ι : Type*} [Field K]
    (P : MvPolynomial ι K) (hP : P.totalDegree ≤ 1) (x y : ι → K) :
    polynomialGradient P x = polynomialGradient P y := by
  funext i
  exact eval_pderiv_eq_of_totalDegree_le_one P hP i x y

/-- A nonsingular quaternary quadratic polynomial cannot be a product of two
affine-linear polynomials. Their two constant gradients cannot span the
gradient image of a nonsingular four-dimensional quadratic form. -/
theorem matrixQuadratic_not_mul_affine {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (h2 : (2 : K) ≠ 0) (P Q : MvPolynomial (Fin 4) K)
    (hP : P.totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1) :
    matrixQuadraticPolynomial A ≠ P * Q := by
  intro hfactor
  let v := polynomialGradient P 0
  let w := polynomialGradient Q 0
  let T : (Fin 4 → K) →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi ![dotProductBilin K K v, dotProductBilin K K w]
  have hdim : Module.finrank K (Fin 2 → K) < Module.finrank K (Fin 4 → K) := by simp
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim)
  have hxv : dotProduct x v = 0 := by
    rw [dotProduct_comm]
    exact congrFun hx 0
  have hxw : dotProduct x w = 0 := by
    rw [dotProduct_comm]
    exact congrFun hx 1
  have hgradient (y : Fin 4 → K) :
      polynomialGradient (matrixQuadraticPolynomial A) y =
        MvPolynomial.eval y Q • v + MvPolynomial.eval y P • w := by
    rw [hfactor]
    have hv := polynomialGradient_eq_of_totalDegree_le_one P hP y 0
    have hw := polynomialGradient_eq_of_totalDegree_le_one Q hQ y 0
    funext i
    change MvPolynomial.eval y (MvPolynomial.pderiv i (P * Q)) = _
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    change polynomialGradient P y i * MvPolynomial.eval y Q +
      MvPolynomial.eval y P * polynomialGradient Q y i = _
    rw [hv, hw]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  apply hx0
  apply (Matrix.nondegenerate_of_det_ne_zero hdet).eq_zero_of_ortho
  intro y
  have hpair : dotProduct x (polynomialGradient (matrixQuadraticPolynomial A) y) = 0 := by
    rw [hgradient, dotProduct_add, dotProduct_smul, dotProduct_smul, hxv, hxw]
    simp
  rw [polynomialGradient_matrixQuadraticPolynomial A hA, dotProduct_smul,
    smul_eq_mul] at hpair
  exact (mul_eq_zero.mp hpair).resolve_left h2

private theorem totalDegree_pos_of_ne_zero_nonunit {K ι : Type*} [Field K]
    (P : MvPolynomial ι K) (hP0 : P ≠ 0) (hPu : ¬ IsUnit P) :
    0 < P.totalDegree := by
  by_contra h
  have hd : P.totalDegree = 0 := Nat.eq_zero_of_not_pos h
  have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : P.coeff 0 ≠ 0 := by
    intro hz
    apply hP0
    rw [heq, hz]
    simp
  apply hPu
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- A nonsingular quaternary quadratic form in odd characteristic is an
irreducible polynomial over its coefficient field. -/
theorem matrixQuadraticPolynomial_irreducible {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.transpose = A) (hdet : A.det ≠ 0)
    (h2 : (2 : K) ≠ 0) : Irreducible (matrixQuadraticPolynomial A) := by
  have hF0 := matrixQuadraticPolynomial_ne_zero A hA hdet h2
  have hdegree := matrixQuadraticPolynomial_totalDegree A hA hdet h2
  refine ⟨?_, ?_⟩
  · intro hunit
    have h := hunit.map (MvPolynomial.eval (0 : Fin 4 → K))
    have hz : MvPolynomial.eval (0 : Fin 4 → K) (matrixQuadraticPolynomial A) = 0 := by
      rw [eval_matrixQuadraticPolynomial]
      simp
    rw [hz] at h
    exact not_isUnit_zero h
  · intro P Q hfactor
    by_contra h
    rcases not_or.mp h with ⟨hPu, hQu⟩
    have hP0 : P ≠ 0 := by
      intro hz
      apply hF0
      rw [hfactor, hz, zero_mul]
    have hQ0 : Q ≠ 0 := by
      intro hz
      apply hF0
      rw [hfactor, hz, mul_zero]
    have hdeg : P.totalDegree + Q.totalDegree = 2 := by
      rw [← MvPolynomial.totalDegree_mul_of_isDomain hP0 hQ0, ← hfactor, hdegree]
    have hPpos := totalDegree_pos_of_ne_zero_nonunit P hP0 hPu
    have hQpos := totalDegree_pos_of_ne_zero_nonunit Q hQ0 hQu
    exact matrixQuadratic_not_mul_affine A hA hdet h2 P Q (by omega) (by omega) hfactor

/-- Irreducibility persists over every field extension, so the projective
quadric is geometrically irreducible in its polynomial presentation. -/
theorem matrixQuadraticPolynomial_irreducible_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (A : Matrix (Fin 4) (Fin 4) K)
    (hA : A.transpose = A) (hdet : A.det ≠ 0) (h2 : (2 : K) ≠ 0) :
    Irreducible ((matrixQuadraticPolynomial A).map f) := by
  rw [matrixQuadraticPolynomial_map]
  apply matrixQuadraticPolynomial_irreducible
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map f) hA
  · intro h
    exact hdet (f.injective ((f.map_det A).trans (h.trans f.map_zero.symm)))
  · intro h
    apply h2
    apply f.injective
    simpa only [map_ofNat, map_zero] using h

end QuaternaryQuadraticForms
