import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Heights and evaluation of fixed integer polynomials

The estimates concern the actual integer coefficients and evaluations.
For a fixed finite family, the constants are chosen before the evaluation
point and before the polynomial whose coefficients supply that point.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The sum of the absolute values of the nonzero integer coefficients. -/
def polynomialCoefficientSum {σ : Type*} (P : MvPolynomial σ ℤ) : ℕ :=
  ∑ d ∈ P.support, (P.coeff d).natAbs

/-- The manuscript's coefficient height, including its lower bound of two. -/
def polynomialCoefficientHeight {σ : Type*} (G : MvPolynomial σ ℤ) : ℕ :=
  max 2 (G.support.sup (fun d => (G.coeff d).natAbs))

/-- The actual coefficient height is at least two. -/
theorem two_le_polynomialCoefficientHeight {σ : Type*} (G : MvPolynomial σ ℤ) :
    2 ≤ polynomialCoefficientHeight G := le_max_left _ _

/-- Every coefficient, including those outside the support, is bounded by
the actual coefficient height. -/
theorem natAbs_coeff_le_polynomialCoefficientHeight {σ : Type*}
    (G : MvPolynomial σ ℤ) (d : σ →₀ ℕ) :
    (G.coeff d).natAbs ≤ polynomialCoefficientHeight G := by
  classical
  by_cases hd : d ∈ G.support
  · exact (Finset.le_sup (f := fun d => (G.coeff d).natAbs) hd).trans
      (le_max_right _ _)
  · rw [MvPolynomial.notMem_support_iff.mp hd]
    exact Nat.zero_le _

private theorem natAbs_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi h =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left h _)

private theorem natAbs_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi h => simp [Finset.prod_insert hi, Int.natAbs_mul, h]

/-- Evaluation is bounded by the coefficient sum times the height to the
actual total degree. Only variables occurring in the polynomial need bounds. -/
theorem natAbs_eval_le_coefficientSum_mul_pow {σ : Type*}
    (P : MvPolynomial σ ℤ) (x : σ → ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hx : ∀ i ∈ P.vars, (x i).natAbs ≤ H) :
    (MvPolynomial.eval x P).natAbs ≤ polynomialCoefficientSum P * H ^ P.totalDegree := by
  classical
  rw [MvPolynomial.eval_eq]
  calc
    (∑ d ∈ P.support, P.coeff d * ∏ i ∈ d.support, x i ^ d i).natAbs ≤
        ∑ d ∈ P.support, (P.coeff d * ∏ i ∈ d.support, x i ^ d i).natAbs :=
      natAbs_finset_sum_le _ _
    _ ≤ ∑ d ∈ P.support, (P.coeff d).natAbs * H ^ P.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Int.natAbs_mul]
      apply Nat.mul_le_mul_left
      rw [natAbs_finset_prod]
      simp only [Int.natAbs_pow]
      calc
        (∏ i ∈ d.support, (x i).natAbs ^ d i) ≤ ∏ i ∈ d.support, H ^ d i := by
          apply Finset.prod_le_prod'
          intro i hi
          exact Nat.pow_le_pow_left (hx i ((MvPolynomial.mem_vars i).mpr ⟨d, hd, hi⟩)) _
        _ = H ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ H ^ P.totalDegree := pow_le_pow_right' hH (MvPolynomial.le_totalDegree hd)
    _ = polynomialCoefficientSum P * H ^ P.totalDegree := by
      rw [polynomialCoefficientSum, Finset.sum_mul]

/-- The same evaluation bound when all coordinates of the evaluation point
are bounded by the chosen height. -/
theorem natAbs_eval_le_coefficientSum_mul_pow_of_forall {σ : Type*}
    (P : MvPolynomial σ ℤ) (x : σ → ℤ) (H : ℕ) (hH : 1 ≤ H)
    (hx : ∀ i, (x i).natAbs ≤ H) :
    (MvPolynomial.eval x P).natAbs ≤ polynomialCoefficientSum P * H ^ P.totalDegree :=
  natAbs_eval_le_coefficientSum_mul_pow P x H hH (fun i _ => hx i)

/-- Fixed positive constants work simultaneously for a finite family of
integer polynomials, independently of the height and evaluation point. -/
theorem finite_polynomial_family_eval_bound {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℤ) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (H : ℕ) (x : σ → ℤ), 1 ≤ H → (∀ i, (x i).natAbs ≤ H) →
        ∀ j ∈ s, (MvPolynomial.eval x (P j)).natAbs ≤ K * H ^ C := by
  classical
  let C := max 1 (s.sup (fun j => (P j).totalDegree))
  let K := max 1 (s.sup (fun j => polynomialCoefficientSum (P j)))
  refine ⟨C, K, le_max_left _ _, le_max_left _ _, ?_⟩
  intro H x hH hx j hj
  have hdegree : (P j).totalDegree ≤ C :=
    (Finset.le_sup (f := fun j => (P j).totalDegree) hj).trans (le_max_right _ _)
  have hcoeff : polynomialCoefficientSum (P j) ≤ K :=
    (Finset.le_sup (f := fun j => polynomialCoefficientSum (P j)) hj).trans
      (le_max_right _ _)
  exact (natAbs_eval_le_coefficientSum_mul_pow_of_forall (P j) x H hH hx).trans
    (Nat.mul_le_mul hcoeff (pow_le_pow_right' hH hdegree))

/-- A fixed finite family has a uniform bound in the actual coefficient
height of any polynomial, for any evaluation tuple bounded by that height. -/
theorem finite_polynomial_family_eval_bound_of_height {ι σ τ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℤ) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (G : MvPolynomial τ ℤ) (x : σ → ℤ),
        (∀ i, (x i).natAbs ≤ polynomialCoefficientHeight G) →
          ∀ j ∈ s, (MvPolynomial.eval x (P j)).natAbs ≤
            K * (polynomialCoefficientHeight G) ^ C := by
  obtain ⟨C, K, hC, hK, h⟩ := finite_polynomial_family_eval_bound s P
  refine ⟨C, K, hC, hK, ?_⟩
  intro G x hx j hj
  exact h (polynomialCoefficientHeight G) x
    ((by decide : 1 ≤ 2).trans (two_le_polynomialCoefficientHeight G)) hx j hj

/-- In particular, evaluating a fixed family on any indexed tuple of the
coefficients of G has constants independent of G and of the coefficient indices. -/
theorem finite_polynomial_family_coeff_eval_bound {ι σ τ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℤ) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (G : MvPolynomial τ ℤ) (indices : σ → τ →₀ ℕ),
        ∀ j ∈ s, (MvPolynomial.eval (fun i => G.coeff (indices i)) (P j)).natAbs ≤
          K * (polynomialCoefficientHeight G) ^ C := by
  obtain ⟨C, K, hC, hK, h⟩ := finite_polynomial_family_eval_bound_of_height (τ := τ) s P
  refine ⟨C, K, hC, hK, ?_⟩
  intro G indices j hj
  exact h G (fun i => G.coeff (indices i))
    (fun i => natAbs_coeff_le_polynomialCoefficientHeight G (indices i)) j hj

end QuaternaryQuadraticForms
