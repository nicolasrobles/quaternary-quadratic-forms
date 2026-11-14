import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Formal differentiation of polynomial substitutions

These identities concern the actual polynomial substitution and partial
derivatives. They provide the chain rule used in the plane-section argument.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- The algebraic chain rule for a finite tuple of polynomial substitutions. -/
theorem pderiv_aeval_chain_rule {R σ τ : Type*} [CommSemiring R] [Fintype σ]
    (G : MvPolynomial σ R) (μ : σ → MvPolynomial τ R) (i : τ) :
    MvPolynomial.pderiv i (MvPolynomial.aeval μ G) =
      ∑ j : σ, MvPolynomial.aeval μ (MvPolynomial.pderiv j G) *
        MvPolynomial.pderiv i (μ j) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add G H hG hH =>
      simp only [map_add, hG, hH, add_mul, Finset.sum_add_distrib]
  | mul_X G k hG =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul,
        map_add, MvPolynomial.pderiv_X, hG]
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ac_rfl
      · simp [Pi.single_apply]

/-- Evaluation commutes with polynomial substitution. -/
theorem eval_aeval_polynomial {R σ τ : Type*} [CommSemiring R]
    (G : MvPolynomial σ R) (μ : σ → MvPolynomial τ R) (x : τ → R) :
    MvPolynomial.eval x (MvPolynomial.aeval μ G) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (μ j)) G := by
  exact (MvPolynomial.eval_assoc μ x G).symm

/-- The chain rule evaluated at a point. -/
theorem eval_pderiv_aeval_chain_rule {R σ τ : Type*} [CommSemiring R] [Fintype σ]
    (G : MvPolynomial σ R) (μ : σ → MvPolynomial τ R) (i : τ) (x : τ → R) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.aeval μ G)) =
      ∑ j : σ,
        MvPolynomial.eval (fun k => MvPolynomial.eval x (μ k)) (MvPolynomial.pderiv j G) *
          MvPolynomial.eval x (MvPolynomial.pderiv i (μ j)) := by
  rw [pderiv_aeval_chain_rule]
  simp only [map_sum, map_mul, eval_aeval_polynomial]

end QuaternaryQuadraticForms
