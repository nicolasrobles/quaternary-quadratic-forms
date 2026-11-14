import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Degree bounds under specialization of polynomial parameters

Replacing some parameters by constants and retaining the others as variables
cannot increase total degree. We prove the slightly more general statement
that any substitution by polynomials of total degree at most one has this
property. The bound uses the original polynomial before any coefficients or
field are chosen, as required for the exceptional-plane resultant family.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Substitution of polynomials of degree at most one does not increase
the total degree. Coefficients may be mapped to any commutative semiring. -/
theorem totalDegree_eval₂_le_of_degree_one
    {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : σ → MvPolynomial τ S)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (MvPolynomial.eval₂ (MvPolynomial.C.comp f) g P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  calc
    ((MvPolynomial.C.comp f) (P.coeff d) *
        ∏ i ∈ d.support, g i ^ d i).totalDegree ≤
        ((MvPolynomial.C.comp f) (P.coeff d)).totalDegree +
          (∏ i ∈ d.support, g i ^ d i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ d.support, g i ^ d i).totalDegree := by
      rw [RingHom.comp_apply, MvPolynomial.totalDegree_C, zero_add]
    _ ≤ ∑ i ∈ d.support, (g i ^ d i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow (g i) (d i)).trans
        (by simpa only [mul_one] using Nat.mul_le_mul_left (d i) (hg i))
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

end QuaternaryQuadraticForms
