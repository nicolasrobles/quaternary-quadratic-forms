import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Dehomogenization of binary forms

The affine polynomial of a binary form is the literal substitution
`g(X, 1)`.  Homogeneity makes this substitution injective at a fixed degree.
The top affine coefficient is the value at the point at infinity `(1 : 0)`.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Substitution of `X` and `1` into a binary polynomial. -/
def binaryDehom {R : Type*} [CommSemiring R]
    (g : MvPolynomial (Fin 2) R) : Polynomial R :=
  MvPolynomial.aeval ![Polynomial.X, 1] g

/-- Evaluating the affine polynomial is evaluating the binary form at `(z,1)`. -/
theorem binaryDehom_eval {R : Type*} [CommSemiring R]
    (g : MvPolynomial (Fin 2) R) (z : R) :
    (binaryDehom g).eval z = MvPolynomial.eval ![z, 1] g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [binaryDehom]
  | add p q hp hq => simp_all [binaryDehom]
  | mul_X p i hp => fin_cases i <;> simp_all [binaryDehom]

/-- Coefficient extension commutes with the same affine substitution. -/
theorem binaryDehom_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : MvPolynomial (Fin 2) R) :
    binaryDehom (g.map f) = (binaryDehom g).map f := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [binaryDehom]
  | add p q hp hq => simp_all [binaryDehom]
  | mul_X p i hp => fin_cases i <;> simp_all [binaryDehom]

/-- Homogenization recovers the original form at its degree of homogeneity. -/
theorem binaryDehom_homogenize {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n) :
    (binaryDehom g).homogenize n = g :=
  Polynomial.homogenize_eq_of_isHomogeneous hg rfl

/-- A nonzero homogeneous form has a nonzero affine polynomial. -/
theorem binaryDehom_ne_zero {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n)
    (hg0 : g ≠ 0) : binaryDehom g ≠ 0 := by
  intro h
  apply hg0
  rw [← binaryDehom_homogenize hg, h, Polynomial.homogenize_zero]

/-- The affine degree cannot exceed the homogeneous degree. -/
theorem binaryDehom_natDegree_le {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n) :
    (binaryDehom g).natDegree ≤ n := by
  classical
  change (MvPolynomial.aeval ![Polynomial.X, 1] g).natDegree ≤ n
  conv_lhs => arg 1; arg 2; rw [g.as_sum]
  rw [MvPolynomial.aeval_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hmn : m 0 + m 1 = n := by
    have := hg (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  simp only [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, mul_one, ← Polynomial.C_eq_algebraMap]
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_X_pow_le _).trans (by omega))

/-- The value of a homogenization at infinity is its degree-`n` coefficient. -/
theorem homogenize_eval_infinity {R : Type*} [CommSemiring R]
    (p : Polynomial R) (n : ℕ) :
    MvPolynomial.eval ![1, 0] (p.homogenize n) = p.coeff n := by
  classical
  rw [Polynomial.homogenize, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single (n, 0)]
  · simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
  · intro b hb hbn
    have hb2 : b.2 ≠ 0 := by
      intro h
      apply hbn
      have := Finset.mem_antidiagonal.mp hb
      exact Prod.ext (by simpa [h] using this) h
    simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, hb2]
  · simp

/-- The top affine coefficient is exactly the value at infinity. -/
theorem binaryDehom_coeff_top {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n) :
    (binaryDehom g).coeff n = MvPolynomial.eval ![1, 0] g := by
  calc
    (binaryDehom g).coeff n =
        MvPolynomial.eval ![1, 0] ((binaryDehom g).homogenize n) :=
      (homogenize_eval_infinity (binaryDehom g) n).symm
    _ = MvPolynomial.eval ![1, 0] g := by rw [binaryDehom_homogenize hg]

/-- The affine degree is exactly `n` precisely when infinity is not a zero. -/
theorem binaryDehom_natDegree_eq_iff {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n)
    (hg0 : g ≠ 0) :
    (binaryDehom g).natDegree = n ↔ MvPolynomial.eval ![1, 0] g ≠ 0 := by
  constructor
  · intro h
    rw [← binaryDehom_coeff_top hg, ← h, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (binaryDehom_ne_zero hg hg0)
  · intro h
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (binaryDehom_natDegree_le hg)
    rwa [binaryDehom_coeff_top hg]

/-- A zero at infinity lowers the affine degree by at least one. -/
theorem binaryDehom_natDegree_lt_of_infinity_zero {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n)
    (hg0 : g ≠ 0) (hinf : MvPolynomial.eval ![1, 0] g = 0) :
    (binaryDehom g).natDegree < n := by
  have hle := binaryDehom_natDegree_le hg
  have hne : (binaryDehom g).natDegree ≠ n := by
    intro h
    exact ((binaryDehom_natDegree_eq_iff hg hg0).mp h) hinf
  omega

end QuaternaryQuadraticForms
