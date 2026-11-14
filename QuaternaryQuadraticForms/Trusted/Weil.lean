import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Registered literature input: the univariate Weil bound

This declaration is an external premise, not a proved manuscript theorem.
Its exact source and hypotheses are registered as `EXT.WEIL` in
`certification/reference_inputs.json`; see the correspondence review in
`certification/correspondence/weil_input.md`.

Katz, *Estimates for nonsingular multiplicative character sums*, published
equation (1.2), states this estimate when all roots of a positive-degree
polynomial are distinct. The author version states it in Section 1, page 1.
Here the field is specialized to `ZMod p`. The actual root set over its
algebraic closure records distinct roots, and `MulChar` extends by zero.
No manuscript-specific projective deduction is included in the premise.
-/

noncomputable section

open scoped BigOperators

axiom QuaternaryQuadraticForms.Trusted.weil_simple_roots
    (p : ℕ) [Fact p.Prime] (ψ : MulChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (f : Polynomial (ZMod p)) (hf : 0 < f.natDegree)
    (hroots : Fintype.card (f.rootSet (AlgebraicClosure (ZMod p))) = f.natDegree) :
    ‖∑ z : ZMod p, ψ (f.eval z)‖ ≤ ((f.natDegree : ℝ) - 1) * Real.sqrt p
