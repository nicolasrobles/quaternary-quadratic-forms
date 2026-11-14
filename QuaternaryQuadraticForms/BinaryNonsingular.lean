import QuaternaryQuadraticForms.BinaryFormRoots
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring

/-!
# Nonsingular binary forms and distinct geometric zeros

The absence of a nonzero common zero of a binary form and its two partial
derivatives implies that its projective geometric zeros are all distinct.
Euler's polynomial identity is used without dividing by the degree.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- A binary form and its two partial derivatives have no common nonzero zero. -/
def BinaryNonsingular {K : Type*} [Field K] (g : MvPolynomial (Fin 2) K) : Prop :=
  ∀ x : Fin 2 → K, x ≠ 0 → MvPolynomial.eval x g = 0 →
    (∀ i : Fin 2, MvPolynomial.eval x (MvPolynomial.pderiv i g) = 0) → False

/-- Nonsingularity excludes the zero polynomial. -/
theorem BinaryNonsingular.ne_zero {K : Type*} [Field K]
    {g : MvPolynomial (Fin 2) K} (h : BinaryNonsingular g) : g ≠ 0 := by
  intro hg
  subst g
  apply h (binaryVector 1 0) binaryVector_infinity_ne_zero (by simp)
  intro i
  simp

/-- Differentiation in the affine variable commutes with dehomogenization. -/
theorem binaryDehom_derivative {R : Type*} [CommSemiring R]
    (g : MvPolynomial (Fin 2) R) :
    (binaryDehom g).derivative = binaryDehom (MvPolynomial.pderiv 0 g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [binaryDehom]
  | add p q hp hq => simp_all [binaryDehom]
  | mul_X p i hp =>
      fin_cases i <;> simp_all [binaryDehom, Polynomial.derivative_mul]
      ring

/-- Euler's identity for a binary form, evaluated at an arbitrary vector. -/
theorem binary_euler_eval {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n)
    (x : Fin 2 → R) :
    x 0 * MvPolynomial.eval x (MvPolynomial.pderiv 0 g) +
      x 1 * MvPolynomial.eval x (MvPolynomial.pderiv 1 g) =
        (n : R) * MvPolynomial.eval x g := by
  have h := congrArg (MvPolynomial.eval x) hg.sum_X_mul_pderiv
  simpa [Fin.sum_univ_two, nsmul_eq_mul] using h

/-- Euler's identity after the literal affine substitution. -/
theorem binaryDehom_euler {R : Type*} [CommSemiring R]
    {g : MvPolynomial (Fin 2) R} {n : ℕ} (hg : g.IsHomogeneous n) :
    Polynomial.X * (binaryDehom g).derivative +
      binaryDehom (MvPolynomial.pderiv 1 g) = n • binaryDehom g := by
  rw [binaryDehom_derivative]
  have h := congrArg (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1]) hg.sum_X_mul_pderiv
  simpa [Fin.sum_univ_two, binaryDehom] using h

/-- A nonsingular binary form has no repeated root in its affine chart. -/
theorem binaryDehom_derivative_ne_zero {K : Type*} [Field K]
    {g : MvPolynomial (Fin 2) K} {n : ℕ} (hg : g.IsHomogeneous n)
    (hns : BinaryNonsingular g) (z : K) (hz : (binaryDehom g).eval z = 0) :
    (binaryDehom g).derivative.eval z ≠ 0 := by
  intro hd
  have hgz : MvPolynomial.eval (binaryVector z 1) g = 0 := by
    simpa only [binaryVector_eq_vec, binaryDehom_eval] using hz
  have h0 : MvPolynomial.eval (binaryVector z 1) (MvPolynomial.pderiv 0 g) = 0 := by
    simpa only [binaryDehom_derivative, binaryDehom_eval, binaryVector_eq_vec] using hd
  have h1 : MvPolynomial.eval (binaryVector z 1) (MvPolynomial.pderiv 1 g) = 0 := by
    simpa [h0, hgz] using binary_euler_eval hg (binaryVector z 1)
  apply hns (binaryVector z 1) (binaryVector_affine_ne_zero z) hgz
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- Over an algebraically closed field, the affine polynomial is separable. -/
theorem binaryDehom_separable_of_nonsingular {K : Type*} [Field K] [IsAlgClosed K]
    {g : MvPolynomial (Fin 2) K} {n : ℕ} (hg : g.IsHomogeneous n)
    (hns : BinaryNonsingular g) : (binaryDehom g).Separable := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).mpr
  intro z
  by_cases hz : (binaryDehom g).eval z = 0
  · right
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
      binaryDehom_derivative_ne_zero hg hns z hz
  · left
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hz

/-- The coefficient of `X f'` at degree `m` is `m` times the coefficient of `f`. -/
theorem coeff_X_mul_derivative {R : Type*} [CommSemiring R]
    (f : Polynomial R) (m : ℕ) :
    (Polynomial.X * f.derivative).coeff m = f.coeff m * (m : R) := by
  cases m with
  | zero => simp
  | succ m => simp [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]

/-- A nonsingular zero at infinity decreases the affine degree by exactly one. -/
theorem binaryDehom_degree_of_nonsingular_infinity {K : Type*} [Field K]
    {g : MvPolynomial (Fin 2) K} {n : ℕ} (hg : g.IsHomogeneous n)
    (hns : BinaryNonsingular g) (hinf : MvPolynomial.eval ![1, 0] g = 0) :
    (binaryDehom g).natDegree = n - 1 := by
  have h0 : MvPolynomial.eval ![1, 0] (MvPolynomial.pderiv 0 g) = 0 := by
    simpa [hinf] using binary_euler_eval hg ![1, 0]
  have h1 : MvPolynomial.eval ![1, 0] (MvPolynomial.pderiv 1 g) ≠ 0 := by
    intro h1
    apply hns (binaryVector 1 0) binaryVector_infinity_ne_zero
      (by simpa only [binaryVector_eq_vec] using hinf)
    intro i
    fin_cases i
    · simpa only [binaryVector_eq_vec] using h0
    · simpa only [binaryVector_eq_vec] using h1
  have hlt := binaryDehom_natDegree_lt_of_infinity_zero hg hns.ne_zero hinf
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (Nat.le_pred_of_lt hlt)
  intro hcoeff
  have hc : (binaryDehom g).coeff (n - 1) = 0 := by
    simpa only [Nat.sub_one] using hcoeff
  have he := congrArg (fun f : Polynomial K => f.coeff (n - 1)) (binaryDehom_euler hg)
  dsimp only at he
  rw [Polynomial.coeff_add, coeff_X_mul_derivative, Polynomial.coeff_smul, hc] at he
  simp only [zero_mul, zero_add, smul_zero] at he
  apply h1
  rw [← binaryDehom_coeff_top (hg.pderiv (i := 1))]
  exact he

open Classical in
/-- A homogeneous nonsingular binary form over an algebraically closed field
has exactly its degree many distinct projective zeros. -/
theorem binaryProjectiveZeros_card_of_nonsingular {K : Type*} [Field K] [IsAlgClosed K]
    {g : MvPolynomial (Fin 2) K} {n : ℕ} (hg : g.IsHomogeneous n)
    (hn : 2 ≤ n) (hns : BinaryNonsingular g) :
    Nat.card (binaryProjectiveZeros g) = n := by
  rw [binaryProjectiveZeros_card hg hns.ne_zero]
  rw [Polynomial.card_rootSet_eq_natDegree (binaryDehom_separable_of_nonsingular hg hns)
    (IsAlgClosed.splits_codomain _)]
  by_cases hinf : MvPolynomial.eval ![1, 0] g = 0
  · rw [if_pos hinf, binaryDehom_degree_of_nonsingular_infinity hg hns hinf]
    omega
  · rw [if_neg hinf, (binaryDehom_natDegree_eq_iff hg hns.ne_zero).mpr hinf]
    exact Nat.add_zero n

/-- The exact geometric-root hypothesis of Corollary 2.6 follows from the
absence of a nonzero geometric common zero of the form and its partial derivatives. -/
theorem binary_nonsingular_geometric_roots {K : Type*} [Field K]
    {g : MvPolynomial (Fin 2) K} {n : ℕ} (hg : g.IsHomogeneous n) (hn : 2 ≤ n)
    (hns : BinaryNonsingular (g.map (algebraMap K (AlgebraicClosure K)))) :
    g ≠ 0 ∧ Nat.card (geometricBinaryProjectiveZeros g) = n := by
  constructor
  · intro hg0
    apply hns.ne_zero
    simp [hg0]
  · exact binaryProjectiveZeros_card_of_nonsingular (hg.map _) hn hns

end QuaternaryQuadraticForms
