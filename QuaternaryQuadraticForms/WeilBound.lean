import QuaternaryQuadraticForms.Trusted.Weil
import QuaternaryQuadraticForms.GeometricRoots

/-!
# The manuscript's univariate estimate

Lemma 2.5 is the registered literature input with the manuscript's explicit
degree parameter. The separable formulation below is deduced using mathlib's
root-count theorem over an algebraic closure.
-/

noncomputable section

namespace QuaternaryQuadraticForms

open scoped BigOperators

/-- Lemma 2.5, with the degree and distinct geometric roots stated explicitly. -/
theorem weil_bound (p : ℕ) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (f : Polynomial (ZMod p)) (m : ℕ) (hm : 1 ≤ m)
    (hdegree : f.natDegree = m)
    (hroots : Fintype.card (f.rootSet (AlgebraicClosure (ZMod p))) = m) :
    ‖∑ z : ZMod p, ψ (f.eval z)‖ ≤ ((m : ℝ) - 1) * Real.sqrt p := by
  subst m
  exact Trusted.weil_simple_roots p ψ hψ f hm hroots

/-- The same trusted estimate after proving the distinct-root condition from
separability. This is the form used by the projective-line deduction. -/
theorem weil_bound_of_separable (p : ℕ) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (f : Polynomial (ZMod p)) (hf : 0 < f.natDegree) (hsep : f.Separable) :
    ‖∑ z : ZMod p, ψ (f.eval z)‖ ≤ ((f.natDegree : ℝ) - 1) * Real.sqrt p :=
  Trusted.weil_simple_roots p ψ hψ f hf (geometricRootCount_eq_natDegree f hsep)

end QuaternaryQuadraticForms
